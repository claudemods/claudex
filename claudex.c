/*
 * claudex - compressed, mountable filesystem images with a custom codec
 *
 * Build:   make            (Arch: sudo pacman -S --needed base-devel fuse3)
 *
 * Usage:
 *   mkfs.claudex create [options] <source-dir> <image>
 *   mkfs.claudex mount   <image> <mountpoint> [-f] [-o options]
 *   mkfs.claudex extract <image> [destination] [-v]
 *   mkfs.claudex test    <image>
 *   mkfs.claudex list    <image>
 *   mkfs.claudex info    <image>
 *   mkfs.claudex initcpio [dir]     install the mkinitcpio boot hook
 *
 * Codec ("CX"): LZ77 with a hash-chain match finder and repeat-distance
 * matches, entropy coded with an adaptive binary range coder (context-
 * modelled literals, lengths and distances). Levels 1-7 parse greedily with
 * lazy matching; levels 8-9 use price-based optimal parsing. Blocks of x86
 * machine code go through a CALL-address filter first.
 *
 * Image format, version 6 (all integers little-endian)
 *
 *   header        96 bytes, see header_encode()
 *   data blocks   the contents of every regular file concatenated into one
 *                 logical "data stream" (similar files next to each other,
 *                 identical files stored once), cut into block_size pieces.
 *                 Each block is CX-compressed on its own (optionally after
 *                 the x86 filter), or stored raw if it would not shrink.
 *   block table   block_count x { uint64 offset, uint32 stored_len, uint8 type, 3 x pad }
 *   metadata      chunks of { uint32 raw_len, uint32 stored_len, uint8 type, data }
 *                 that decode to node_count entries of:
 *                   uint32 path_len, path bytes   (relative, "" = root directory)
 *                   uint32 mode, uint32 uid, uint32 gid,
 *                   int64 mtime, uint32 mtime_nsec, int64 atime, uint32 atime_nsec
 *                   S_IFREG: uint64 data_offset, uint64 size, uint32 crc32,
 *                            uint32 hard_link (index of an earlier entry this
 *                            is a hard link to, or 0xFFFFFFFF)
 *                   S_IFLNK: uint32 target_len, target bytes
 *                   S_IFCHR/S_IFBLK/S_IFIFO/S_IFSOCK: uint64 rdev
 *                   uint32 xattr_count, then per extended attribute (ACLs,
 *                   capabilities, labels...): uint32 name_len, name,
 *                   uint32 value_len, value
 *                 Parents always precede their contents.
 *   footer        "CLDE" uint32 node_count
 *
 * A file is the byte range [data_offset, data_offset + size) of the data
 * stream, so reading any part of it only needs the blocks that cover it.
 */

#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#define FUSE_USE_VERSION 31
#include <fuse.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <stdint.h>
#include <inttypes.h>
#include <fnmatch.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/statvfs.h>
#include <sys/xattr.h>

#define MAGIC              "CLDX"
#define FOOTER_MAGIC       "CLDE"
#define FORMAT_VERSION     6
#define NO_LINK            UINT32_MAX
#define HEADER_SIZE        96
#define BLOCK_ENTRY_SIZE   16
#define CHUNK_HEADER_SIZE  9
#define FOOTER_SIZE        8
#define DEFAULT_BLOCK_SIZE (1u << 20)
#define MIN_BLOCK_SIZE     (64u << 10)
#define MAX_BLOCK_SIZE     (64u << 20)
#define DEFAULT_LEVEL      9
#define MAX_LEVEL          9
#define MAX_PATH_LEN       8192
#define MAX_META_SIZE      ((uint64_t)16 << 30)
#define MAX_THREADS        64
#define DEDUP_MIN_SIZE     4096         // smaller duplicates already compress away inside solid blocks
#define NO_DUP             UINT32_MAX

#define BLOCK_STORED 0
#define BLOCK_CX     1
#define BLOCK_CX_X86 2      // CX after the x86 call-address filter (programs and libraries)

/* =====================================================================
 *  Little-endian helpers and CRC-32
 * ===================================================================== */

static inline void put_le32(uint8_t *p, uint32_t v) {
    p[0] = v & 0xFF; p[1] = (v >> 8) & 0xFF; p[2] = (v >> 16) & 0xFF; p[3] = (v >> 24) & 0xFF;
}

static inline void put_le64(uint8_t *p, uint64_t v) {
    put_le32(p, (uint32_t)v);
    put_le32(p + 4, (uint32_t)(v >> 32));
}

static inline uint32_t get_le32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static inline uint64_t get_le64(const uint8_t *p) {
    return (uint64_t)get_le32(p) | ((uint64_t)get_le32(p + 4) << 32);
}

static uint32_t crc_tab[8][256];

__attribute__((constructor))
static void crc_init(void) {
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
        crc_tab[0][i] = c;
    }
    for (int k = 1; k < 8; k++) {
        for (uint32_t i = 0; i < 256; i++) {
            crc_tab[k][i] = (crc_tab[k - 1][i] >> 8) ^ crc_tab[0][crc_tab[k - 1][i] & 0xFF];
        }
    }
}

// CRC-32 (slicing-by-8)
static uint32_t crc32_update(uint32_t crc, const void *data, size_t len) {
    const uint8_t *p = data;
    crc = ~crc;
    while (len >= 8) {
        uint32_t one = get_le32(p) ^ crc;
        uint32_t two = get_le32(p + 4);
        crc = crc_tab[7][one & 0xFF] ^ crc_tab[6][(one >> 8) & 0xFF] ^
              crc_tab[5][(one >> 16) & 0xFF] ^ crc_tab[4][one >> 24] ^
              crc_tab[3][two & 0xFF] ^ crc_tab[2][(two >> 8) & 0xFF] ^
              crc_tab[1][(two >> 16) & 0xFF] ^ crc_tab[0][two >> 24];
        p += 8;
        len -= 8;
    }
    while (len--) crc = crc_tab[0][(crc ^ *p++) & 0xFF] ^ (crc >> 8);
    return ~crc;
}

/* =====================================================================
 *  CX codec: LZ77 + adaptive binary range coder
 * ===================================================================== */

#define CX_PROB_BITS   11
#define CX_PROB_INIT   (1u << (CX_PROB_BITS - 1))
#define CX_MOVE_BITS   5
#define CX_TOP         (1u << 24)
#define CX_STATES      12
#define CX_POS_STATES  4
#define CX_LIT_CTX     3
#define CX_MIN_MATCH   2
#define CX_MAX_MATCH   273
#define CX_HASH_BITS   18

typedef uint16_t prob_t;

typedef struct {
    prob_t choice;
    prob_t choice2;
    prob_t low[CX_POS_STATES][8];
    prob_t mid[CX_POS_STATES][8];
    prob_t high[256];
} len_model_t;

// Everything is a prob_t, so the model can be reset as one flat array
typedef struct {
    prob_t is_match[CX_STATES][CX_POS_STATES];
    prob_t is_rep[CX_STATES];
    prob_t is_rep0[CX_STATES];
    prob_t is_rep1[CX_STATES];
    prob_t is_rep2[CX_STATES];
    prob_t is_rep0_long[CX_STATES][CX_POS_STATES];
    prob_t lit[1 << CX_LIT_CTX][0x300];
    prob_t slot[4][64];
    prob_t spec[14][64];
    prob_t align[16];
    len_model_t len;
    len_model_t rep_len;
} model_t;

static void model_init(model_t *m) {
    prob_t *p = (prob_t*)m;
    for (size_t i = 0; i < sizeof(model_t) / sizeof(prob_t); i++) p[i] = CX_PROB_INIT;
}

// States 0-6: last packet was a literal; 7-11: last packet was a match/rep
static inline uint32_t st_lit(uint32_t s)   { return s < 4 ? 0 : (s < 10 ? s - 3 : s - 6); }
static inline uint32_t st_match(uint32_t s) { return s < 7 ? 7 : 10; }
static inline uint32_t st_rep(uint32_t s)   { return s < 7 ? 8 : 11; }
static inline uint32_t st_short(uint32_t s) { return s < 7 ? 9 : 11; }

/* ---------- range encoder ---------- */

typedef struct {
    uint64_t low;
    uint32_t range;
    uint8_t cache;
    uint64_t cache_size;
    uint8_t *out;
    size_t pos;
    size_t cap;
    int overflow;
} rc_enc_t;

static void rc_enc_init(rc_enc_t *rc, uint8_t *out, size_t cap) {
    rc->low = 0;
    rc->range = 0xFFFFFFFFu;
    rc->cache = 0;
    rc->cache_size = 1;
    rc->out = out;
    rc->pos = 0;
    rc->cap = cap;
    rc->overflow = 0;
}

static inline void rc_out(rc_enc_t *rc, uint8_t b) {
    if (rc->pos < rc->cap) rc->out[rc->pos++] = b;
    else rc->overflow = 1;
}

static void rc_shift_low(rc_enc_t *rc) {
    if ((uint32_t)rc->low < 0xFF000000u || (rc->low >> 32) != 0) {
        uint8_t carry = (uint8_t)(rc->low >> 32);
        uint8_t temp = rc->cache;
        do {
            rc_out(rc, (uint8_t)(temp + carry));
            temp = 0xFF;
        } while (--rc->cache_size != 0);
        rc->cache = (uint8_t)(rc->low >> 24);
    }
    rc->cache_size++;
    rc->low = (rc->low & 0x00FFFFFFu) << 8;
}

static void rc_flush(rc_enc_t *rc) {
    for (int i = 0; i < 5; i++) rc_shift_low(rc);
}

static inline void rc_bit(rc_enc_t *rc, prob_t *p, uint32_t bit) {
    uint32_t bound = (rc->range >> CX_PROB_BITS) * *p;
    if (!bit) {
        rc->range = bound;
        *p += ((1u << CX_PROB_BITS) - *p) >> CX_MOVE_BITS;
    } else {
        rc->low += bound;
        rc->range -= bound;
        *p -= *p >> CX_MOVE_BITS;
    }
    while (rc->range < CX_TOP) {
        rc->range <<= 8;
        rc_shift_low(rc);
    }
}

static void rc_direct(rc_enc_t *rc, uint32_t value, int nbits) {
    for (int i = nbits - 1; i >= 0; i--) {
        rc->range >>= 1;
        if ((value >> i) & 1) rc->low += rc->range;
        while (rc->range < CX_TOP) {
            rc->range <<= 8;
            rc_shift_low(rc);
        }
    }
}

static void enc_tree(rc_enc_t *rc, prob_t *probs, int nbits, uint32_t sym) {
    uint32_t m = 1;
    for (int i = nbits - 1; i >= 0; i--) {
        uint32_t b = (sym >> i) & 1;
        rc_bit(rc, &probs[m], b);
        m = (m << 1) | b;
    }
}

static void enc_rtree(rc_enc_t *rc, prob_t *probs, int nbits, uint32_t sym) {
    uint32_t m = 1;
    for (int i = 0; i < nbits; i++) {
        uint32_t b = sym & 1;
        sym >>= 1;
        rc_bit(rc, &probs[m], b);
        m = (m << 1) | b;
    }
}

// Literal coded with the byte at the last match distance as extra context
static void enc_matched_lit(rc_enc_t *rc, prob_t *probs, uint32_t byte, uint32_t match_byte) {
    uint32_t sym = 1;
    int matched = 1;
    for (int i = 7; i >= 0; i--) {
        uint32_t bit = (byte >> i) & 1;
        if (matched) {
            uint32_t mbit = (match_byte >> i) & 1;
            rc_bit(rc, &probs[0x100 + (mbit << 8) + sym], bit);
            matched = (bit == mbit);
        } else {
            rc_bit(rc, &probs[sym], bit);
        }
        sym = (sym << 1) | bit;
    }
}

static void enc_len(rc_enc_t *rc, len_model_t *lm, uint32_t len, uint32_t ps) {
    len -= CX_MIN_MATCH;
    if (len < 8) {
        rc_bit(rc, &lm->choice, 0);
        enc_tree(rc, lm->low[ps], 3, len);
    } else if (len < 16) {
        rc_bit(rc, &lm->choice, 1);
        rc_bit(rc, &lm->choice2, 0);
        enc_tree(rc, lm->mid[ps], 3, len - 8);
    } else {
        rc_bit(rc, &lm->choice, 1);
        rc_bit(rc, &lm->choice2, 1);
        enc_tree(rc, lm->high, 8, len - 16);
    }
}

// d = distance - 1
static void enc_dist(rc_enc_t *rc, model_t *m, uint32_t d, uint32_t len) {
    uint32_t ls = len - CX_MIN_MATCH;
    if (ls > 3) ls = 3;
    uint32_t slot;
    if (d < 4) {
        slot = d;
    } else {
        uint32_t n = 31 - (uint32_t)__builtin_clz(d);
        slot = (n << 1) | ((d >> (n - 1)) & 1);
    }
    enc_tree(rc, m->slot[ls], 6, slot);
    if (slot >= 4) {
        uint32_t fb = (slot >> 1) - 1;
        uint32_t rem = d - ((2 | (slot & 1)) << fb);
        if (slot < 14) {
            enc_rtree(rc, m->spec[slot], (int)fb, rem);
        } else {
            rc_direct(rc, rem >> 4, (int)fb - 4);
            enc_rtree(rc, m->align, 4, rem & 15);
        }
    }
}

/* ---------- range decoder ---------- */

typedef struct {
    uint32_t range;
    uint32_t code;
    const uint8_t *in;
    size_t pos;
    size_t len;
    int overrun;
} rc_dec_t;

static inline uint8_t rc_in(rc_dec_t *rc) {
    if (rc->pos < rc->len) return rc->in[rc->pos++];
    rc->overrun = 1;
    return 0;
}

static inline uint32_t rc_dbit(rc_dec_t *rc, prob_t *p) {
    uint32_t bound = (rc->range >> CX_PROB_BITS) * *p;
    uint32_t bit;
    if (rc->code < bound) {
        rc->range = bound;
        *p += ((1u << CX_PROB_BITS) - *p) >> CX_MOVE_BITS;
        bit = 0;
    } else {
        rc->code -= bound;
        rc->range -= bound;
        *p -= *p >> CX_MOVE_BITS;
        bit = 1;
    }
    while (rc->range < CX_TOP) {
        rc->range <<= 8;
        rc->code = (rc->code << 8) | rc_in(rc);
    }
    return bit;
}

static uint32_t rc_ddirect(rc_dec_t *rc, int nbits) {
    uint32_t v = 0;
    for (int i = 0; i < nbits; i++) {
        rc->range >>= 1;
        uint32_t bit = 0;
        if (rc->code >= rc->range) {
            rc->code -= rc->range;
            bit = 1;
        }
        v = (v << 1) | bit;
        while (rc->range < CX_TOP) {
            rc->range <<= 8;
            rc->code = (rc->code << 8) | rc_in(rc);
        }
    }
    return v;
}

static uint32_t dec_tree(rc_dec_t *rc, prob_t *probs, int nbits) {
    uint32_t m = 1;
    for (int i = 0; i < nbits; i++) m = (m << 1) | rc_dbit(rc, &probs[m]);
    return m - (1u << nbits);
}

static uint32_t dec_rtree(rc_dec_t *rc, prob_t *probs, int nbits) {
    uint32_t m = 1, sym = 0;
    for (int i = 0; i < nbits; i++) {
        uint32_t b = rc_dbit(rc, &probs[m]);
        m = (m << 1) | b;
        sym |= b << i;
    }
    return sym;
}

static uint32_t dec_matched_lit(rc_dec_t *rc, prob_t *probs, uint32_t match_byte) {
    uint32_t sym = 1;
    int matched = 1;
    for (int i = 7; i >= 0; i--) {
        uint32_t bit;
        if (matched) {
            uint32_t mbit = (match_byte >> i) & 1;
            bit = rc_dbit(rc, &probs[0x100 + (mbit << 8) + sym]);
            matched = (bit == mbit);
        } else {
            bit = rc_dbit(rc, &probs[sym]);
        }
        sym = (sym << 1) | bit;
    }
    return sym & 0xFF;
}

static uint32_t dec_len(rc_dec_t *rc, len_model_t *lm, uint32_t ps) {
    if (!rc_dbit(rc, &lm->choice)) return CX_MIN_MATCH + dec_tree(rc, lm->low[ps], 3);
    if (!rc_dbit(rc, &lm->choice2)) return CX_MIN_MATCH + 8 + dec_tree(rc, lm->mid[ps], 3);
    return CX_MIN_MATCH + 16 + dec_tree(rc, lm->high, 8);
}

// Returns distance - 1
static uint32_t dec_dist(rc_dec_t *rc, model_t *m, uint32_t len) {
    uint32_t ls = len - CX_MIN_MATCH;
    if (ls > 3) ls = 3;
    uint32_t slot = dec_tree(rc, m->slot[ls], 6);
    if (slot < 4) return slot;
    uint32_t fb = (slot >> 1) - 1;
    uint32_t base = (2 | (slot & 1)) << fb;
    if (slot < 14) return base + dec_rtree(rc, m->spec[slot], (int)fb);
    return base + (rc_ddirect(rc, (int)fb - 4) << 4) + dec_rtree(rc, m->align, 4);
}

/* Decodes exactly out_len bytes. Returns 0, or -1 if the data is corrupt. */
static int cx_decompress(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_len, model_t *m) {
    if (in_len < 5 || in[0] != 0) return -1;

    rc_dec_t rc = { .range = 0xFFFFFFFFu, .code = 0, .in = in, .pos = 0, .len = in_len, .overrun = 0 };
    for (int i = 0; i < 5; i++) rc.code = (rc.code << 8) | rc_in(&rc);
    model_init(m);

    uint32_t state = 0;
    uint32_t reps[4] = { 1, 1, 1, 1 };
    size_t pos = 0;

    while (pos < out_len) {
        uint32_t ps = (uint32_t)pos & (CX_POS_STATES - 1);

        if (!rc_dbit(&rc, &m->is_match[state][ps])) {
            prob_t *probs = m->lit[(pos ? out[pos - 1] : 0) >> (8 - CX_LIT_CTX)];
            uint32_t sym;
            if (state >= 7) {
                if (reps[0] > pos) return -1;
                sym = dec_matched_lit(&rc, probs, out[pos - reps[0]]);
            } else {
                sym = dec_tree(&rc, probs, 8);
            }
            out[pos++] = (uint8_t)sym;
            state = st_lit(state);
        } else {
            uint32_t len;
            if (!rc_dbit(&rc, &m->is_rep[state])) {
                len = dec_len(&rc, &m->len, ps);
                uint32_t d = dec_dist(&rc, m, len);
                reps[3] = reps[2];
                reps[2] = reps[1];
                reps[1] = reps[0];
                reps[0] = d + 1;            // wraps to 0 on garbage, rejected below
                state = st_match(state);
            } else {
                if (!rc_dbit(&rc, &m->is_rep0[state])) {
                    if (!rc_dbit(&rc, &m->is_rep0_long[state][ps])) {
                        // short rep: one byte from the last distance
                        if (reps[0] == 0 || reps[0] > pos) return -1;
                        out[pos] = out[pos - reps[0]];
                        pos++;
                        state = st_short(state);
                        if (rc.overrun) return -1;
                        continue;
                    }
                } else {
                    uint32_t d;
                    if (!rc_dbit(&rc, &m->is_rep1[state])) {
                        d = reps[1];
                    } else {
                        if (!rc_dbit(&rc, &m->is_rep2[state])) {
                            d = reps[2];
                        } else {
                            d = reps[3];
                            reps[3] = reps[2];
                        }
                        reps[2] = reps[1];
                    }
                    reps[1] = reps[0];
                    reps[0] = d;
                }
                len = dec_len(&rc, &m->rep_len, ps);
                state = st_rep(state);
            }

            uint32_t dist = reps[0];
            if (dist == 0 || dist > pos || len > out_len - pos) return -1;
            uint8_t *dst = out + pos;
            const uint8_t *src = dst - dist;
            for (uint32_t i = 0; i < len; i++) dst[i] = src[i];   // overlap-safe
            pos += len;
        }
        if (rc.overrun) return -1;
    }
    return 0;
}

/* ---------- encoder ---------- */

#define OPT_NUM    4096         // positions the optimal parser looks ahead
#define PRICE_INF  0x3FFFFFFFu

enum { OP_LIT, OP_SHORTREP, OP_REP, OP_MATCH };

typedef struct {
    uint32_t state;
    uint32_t reps[4];
} cx_state_t;

// One position in the optimal parser: cheapest known way to reach it
typedef struct {
    uint32_t price;
    uint32_t prev;          // node this packet starts from
    uint32_t len;
    uint32_t arg;           // rep index or match distance
    uint8_t op;
    cx_state_t st;
} opt_node_t;

// Bit costs (1/16 bit units) taken from the current model
typedef struct {
    uint32_t len[2][CX_POS_STATES][CX_MAX_MATCH + 1];   // [0] matches, [1] reps
    uint32_t slot[4][64];
    uint32_t dist_small[4][128];
    uint32_t align[16];
} pricer_t;

typedef struct {
    uint32_t chain;         // match candidates to try per position
    uint32_t nice;          // stop searching at this length
    int lazy;
    int optimal;            // price-based optimal parsing (levels 8-9)
    uint32_t capacity;
    int32_t *head;
    int32_t *prev;
    uint32_t ins;           // next position to insert into the hash chains
    opt_node_t *opt;
    uint32_t *path;
    pricer_t prices;
    model_t model;
} cx_enc_t;

static void cx_enc_free(cx_enc_t *e) {
    if (!e) return;
    free(e->head);
    free(e->prev);
    free(e->opt);
    free(e->path);
    free(e);
}

static cx_enc_t* cx_enc_create(int level, uint32_t capacity) {
    static const uint32_t chain[MAX_LEVEL + 1] = { 0, 4, 8, 16, 32, 64, 128, 256, 128, 512 };
    static const uint32_t nice[MAX_LEVEL + 1]  = { 0, 16, 24, 32, 48, 64, 96, 128, 64, 128 };
    if (level < 1) level = 1;
    if (level > MAX_LEVEL) level = MAX_LEVEL;

    cx_enc_t *e = calloc(1, sizeof(cx_enc_t));
    if (!e) return NULL;
    e->chain = chain[level];
    e->nice = nice[level];
    e->lazy = level >= 3;
    e->optimal = level >= 8;
    e->capacity = capacity;
    e->head = malloc(sizeof(int32_t) << CX_HASH_BITS);
    e->prev = malloc((size_t)capacity * sizeof(int32_t));
    if (e->optimal) {
        e->opt = malloc(OPT_NUM * sizeof(opt_node_t));
        e->path = malloc(OPT_NUM * sizeof(uint32_t));
    }
    if (!e->head || !e->prev || (e->optimal && (!e->opt || !e->path))) {
        cx_enc_free(e);
        return NULL;
    }
    return e;
}

static inline uint32_t hash3(const uint8_t *p) {
    return (((uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16)) * 2654435761u) >> (32 - CX_HASH_BITS);
}

static void ensure_inserted(cx_enc_t *e, const uint8_t *in, uint32_t n, uint32_t target) {
    while (e->ins < target) {
        if (e->ins + 3 <= n) {
            uint32_t h = hash3(in + e->ins);
            e->prev[e->ins] = e->head[h];
            e->head[h] = (int32_t)e->ins;
        }
        e->ins++;
    }
}

// Longest earlier match at pos (length >= 3), or 0. Positions < pos must be inserted.
static uint32_t find_match(cx_enc_t *e, const uint8_t *in, uint32_t n, uint32_t pos, uint32_t *dist) {
    if (pos + 3 > n) return 0;
    uint32_t max_len = n - pos;
    if (max_len > CX_MAX_MATCH) max_len = CX_MAX_MATCH;

    int32_t cand = e->head[hash3(in + pos)];
    uint32_t best = 0, best_dist = 0, chain = e->chain;
    while (cand >= 0 && chain-- > 0) {
        uint32_t c = (uint32_t)cand;
        // best < max_len always holds here, so this index is in range
        if (in[c + best] == in[pos + best]) {
            uint32_t len = 0;
            while (len < max_len && in[c + len] == in[pos + len]) len++;
            if (len > best) {
                best = len;
                best_dist = pos - c;
                if (len >= e->nice || len == max_len) break;
            }
        }
        cand = e->prev[c];
    }
    if (best < 3) return 0;
    // A short match far away costs more bits than three literals
    if (best == 3 && best_dist >= (1u << 15)) return 0;
    *dist = best_dist;
    return best;
}

// Every match (length >= 3) that beats the previous one, shortest first. Returns the count.
static uint32_t find_matches(cx_enc_t *e, const uint8_t *in, uint32_t n, uint32_t pos, uint32_t *lens, uint32_t *dists) {
    if (pos + 3 > n) return 0;
    uint32_t max_len = n - pos;
    if (max_len > CX_MAX_MATCH) max_len = CX_MAX_MATCH;

    int32_t cand = e->head[hash3(in + pos)];
    uint32_t best = 2, count = 0, chain = e->chain;
    while (cand >= 0 && chain-- > 0) {
        uint32_t c = (uint32_t)cand;
        if (in[c + best] == in[pos + best]) {
            uint32_t len = 0;
            while (len < max_len && in[c + len] == in[pos + len]) len++;
            if (len > best) {
                best = len;
                lens[count] = len;
                dists[count] = pos - c;
                count++;
                if (len >= e->nice || len == max_len) break;
            }
        }
        cand = e->prev[c];
    }
    return count;
}

static inline void reps_use(uint32_t reps[4], uint32_t idx) {
    uint32_t d = reps[idx];
    for (uint32_t k = idx; k > 0; k--) reps[k] = reps[k - 1];
    reps[0] = d;
}

static inline void reps_push(uint32_t reps[4], uint32_t dist) {
    reps[3] = reps[2];
    reps[2] = reps[1];
    reps[1] = reps[0];
    reps[0] = dist;
}

/* ---------- packet emitters (shared by both parsers) ---------- */

static void emit_literal(rc_enc_t *rc, model_t *m, const uint8_t *in, uint32_t pos, cx_state_t *s) {
    uint32_t ps = pos & (CX_POS_STATES - 1);
    rc_bit(rc, &m->is_match[s->state][ps], 0);
    prob_t *probs = m->lit[(pos ? in[pos - 1] : 0) >> (8 - CX_LIT_CTX)];
    if (s->state >= 7) enc_matched_lit(rc, probs, in[pos], in[pos - s->reps[0]]);
    else enc_tree(rc, probs, 8, in[pos]);
    s->state = st_lit(s->state);
}

static void emit_match(rc_enc_t *rc, model_t *m, uint32_t pos, cx_state_t *s, uint32_t len, uint32_t dist) {
    uint32_t ps = pos & (CX_POS_STATES - 1);
    rc_bit(rc, &m->is_match[s->state][ps], 1);
    rc_bit(rc, &m->is_rep[s->state], 0);
    enc_len(rc, &m->len, len, ps);
    enc_dist(rc, m, dist - 1, len);
    reps_push(s->reps, dist);
    s->state = st_match(s->state);
}

static void emit_rep(rc_enc_t *rc, model_t *m, uint32_t pos, cx_state_t *s, uint32_t idx, uint32_t len) {
    uint32_t ps = pos & (CX_POS_STATES - 1);
    rc_bit(rc, &m->is_match[s->state][ps], 1);
    rc_bit(rc, &m->is_rep[s->state], 1);
    if (idx == 0) {
        rc_bit(rc, &m->is_rep0[s->state], 0);
        rc_bit(rc, &m->is_rep0_long[s->state][ps], 1);
    } else {
        rc_bit(rc, &m->is_rep0[s->state], 1);
        if (idx == 1) {
            rc_bit(rc, &m->is_rep1[s->state], 0);
        } else {
            rc_bit(rc, &m->is_rep1[s->state], 1);
            rc_bit(rc, &m->is_rep2[s->state], idx == 3);
        }
        reps_use(s->reps, idx);
    }
    enc_len(rc, &m->rep_len, len, ps);
    s->state = st_rep(s->state);
}

static void emit_shortrep(rc_enc_t *rc, model_t *m, uint32_t pos, cx_state_t *s) {
    uint32_t ps = pos & (CX_POS_STATES - 1);
    rc_bit(rc, &m->is_match[s->state][ps], 1);
    rc_bit(rc, &m->is_rep[s->state], 1);
    rc_bit(rc, &m->is_rep0[s->state], 0);
    rc_bit(rc, &m->is_rep0_long[s->state][ps], 0);
    s->state = st_short(s->state);
}

static void enc_begin(cx_enc_t *e, rc_enc_t *rc, uint8_t *out, size_t cap) {
    model_init(&e->model);
    memset(e->head, 0xFF, sizeof(int32_t) << CX_HASH_BITS);   // all -1
    e->ins = 0;
    rc_enc_init(rc, out, cap);
}

/* ---------- fast parser (levels 1-7): greedy with lazy matching ---------- */

static size_t cx_compress_fast(cx_enc_t *e, const uint8_t *in, uint32_t n, uint8_t *out, size_t cap) {
    rc_enc_t rc;
    enc_begin(e, &rc, out, cap);
    model_t *m = &e->model;

    cx_state_t s = { 0, { 1, 1, 1, 1 } };
    uint32_t pos = 0;
    uint32_t cached_pos = UINT32_MAX, cached_len = 0, cached_dist = 0;

    while (pos < n) {
        if (rc.overflow) return 0;
        uint32_t max_len = n - pos;
        if (max_len > CX_MAX_MATCH) max_len = CX_MAX_MATCH;

        // Repeat distances are the cheapest matches
        uint32_t rep_len = 0, rep_idx = 0;
        if (max_len >= CX_MIN_MATCH) {
            for (uint32_t r = 0; r < 4; r++) {
                uint32_t d = s.reps[r];
                if (d > pos) continue;
                uint32_t len = 0;
                while (len < max_len && in[pos + len] == in[pos + len - d]) len++;
                if (len > rep_len) {
                    rep_len = len;
                    rep_idx = r;
                }
            }
        }

        uint32_t main_len = 0, main_dist = 0;
        if (rep_len < e->nice) {
            if (cached_pos == pos) {
                main_len = cached_len;
                main_dist = cached_dist;
            } else {
                ensure_inserted(e, in, n, pos);
                main_len = find_match(e, in, n, pos, &main_dist);
            }
        }

        int use_rep = rep_len >= CX_MIN_MATCH &&
                      (rep_len >= e->nice || rep_len + 1 >= main_len ||
                       (rep_len + 2 >= main_len && main_dist >= 512) ||
                       (rep_len + 3 >= main_len && main_dist >= 32768));

        if (!use_rep && main_len >= 3 && main_len < e->nice && e->lazy && pos + 1 < n) {
            // Lazy matching: emit a literal if the next position has a clearly better match
            ensure_inserted(e, in, n, pos + 1);
            uint32_t d2 = 0;
            uint32_t l2 = find_match(e, in, n, pos + 1, &d2);
            cached_pos = pos + 1;
            cached_len = l2;
            cached_dist = d2;
            if ((l2 >= main_len && d2 < main_dist) ||
                (l2 == main_len + 1 && (d2 >> 7) <= main_dist) ||
                l2 > main_len + 1) {
                main_len = 0;
            }
        }

        if (use_rep) {
            emit_rep(&rc, m, pos, &s, rep_idx, rep_len);
            pos += rep_len;
        } else if (main_len >= 3) {
            emit_match(&rc, m, pos, &s, main_len, main_dist);
            pos += main_len;
        } else {
            emit_literal(&rc, m, in, pos, &s);
            pos++;
        }
    }

    rc_flush(&rc);
    return rc.overflow ? 0 : rc.pos;
}

/* ---------- optimal parser (levels 8-9) ----------
 * Looks ahead up to OPT_NUM positions and picks the sequence of literals,
 * matches and repeats with the lowest total bit cost under the current
 * probability model, instead of always taking the longest match. */

static uint32_t g_prob_prices[(1u << CX_PROB_BITS) >> 4];

__attribute__((constructor))
static void price_init(void) {
    // -log2(probability) in 1/16 bit units, integer-only
    for (uint32_t i = 0; i < ((1u << CX_PROB_BITS) >> 4); i++) {
        uint32_t w = (i << 4) + 8;
        uint32_t bits = 0;
        for (int j = 0; j < 4; j++) {
            w = w * w;
            bits <<= 1;
            while (w >= (1u << 16)) {
                w >>= 1;
                bits++;
            }
        }
        g_prob_prices[i] = (CX_PROB_BITS << 4) - 15 - bits;
    }
}

static inline uint32_t bit_price(prob_t p, uint32_t bit) {
    return g_prob_prices[(bit ? (1u << CX_PROB_BITS) - p : p) >> 4];
}

static uint32_t tree_price(const prob_t *probs, int nbits, uint32_t sym) {
    uint32_t price = 0, m = 1;
    for (int i = nbits - 1; i >= 0; i--) {
        uint32_t b = (sym >> i) & 1;
        price += bit_price(probs[m], b);
        m = (m << 1) | b;
    }
    return price;
}

static uint32_t rtree_price(const prob_t *probs, int nbits, uint32_t sym) {
    uint32_t price = 0, m = 1;
    for (int i = 0; i < nbits; i++) {
        uint32_t b = sym & 1;
        sym >>= 1;
        price += bit_price(probs[m], b);
        m = (m << 1) | b;
    }
    return price;
}

static uint32_t literal_price(const model_t *m, const uint8_t *in, uint32_t pos, const cx_state_t *s) {
    const prob_t *probs = m->lit[(pos ? in[pos - 1] : 0) >> (8 - CX_LIT_CTX)];
    uint32_t byte = in[pos];
    if (s->state < 7) return tree_price(probs, 8, byte);

    uint32_t match_byte = in[pos - s->reps[0]];
    uint32_t price = 0, sym = 1;
    int matched = 1;
    for (int i = 7; i >= 0; i--) {
        uint32_t bit = (byte >> i) & 1;
        if (matched) {
            uint32_t mbit = (match_byte >> i) & 1;
            price += bit_price(probs[0x100 + (mbit << 8) + sym], bit);
            matched = (bit == mbit);
        } else {
            price += bit_price(probs[sym], bit);
        }
        sym = (sym << 1) | bit;
    }
    return price;
}

static inline uint32_t dist_slot(uint32_t d) {
    if (d < 4) return d;
    uint32_t n = 31 - (uint32_t)__builtin_clz(d);
    return (n << 1) | ((d >> (n - 1)) & 1);
}

static void fill_prices(cx_enc_t *e) {
    const model_t *m = &e->model;
    pricer_t *pr = &e->prices;

    for (int k = 0; k < 2; k++) {
        const len_model_t *lm = k ? &m->rep_len : &m->len;
        for (uint32_t ps = 0; ps < CX_POS_STATES; ps++) {
            for (uint32_t len = CX_MIN_MATCH; len <= CX_MAX_MATCH; len++) {
                uint32_t l = len - CX_MIN_MATCH;
                uint32_t price;
                if (l < 8) {
                    price = bit_price(lm->choice, 0) + tree_price(lm->low[ps], 3, l);
                } else if (l < 16) {
                    price = bit_price(lm->choice, 1) + bit_price(lm->choice2, 0) + tree_price(lm->mid[ps], 3, l - 8);
                } else {
                    price = bit_price(lm->choice, 1) + bit_price(lm->choice2, 1) + tree_price(lm->high, 8, l - 16);
                }
                pr->len[k][ps][len] = price;
            }
        }
    }
    for (uint32_t ls = 0; ls < 4; ls++) {
        for (uint32_t slot = 0; slot < 64; slot++) pr->slot[ls][slot] = tree_price(m->slot[ls], 6, slot);
        for (uint32_t d = 0; d < 128; d++) {
            uint32_t slot = dist_slot(d);
            uint32_t price = pr->slot[ls][slot];
            if (slot >= 4) {
                uint32_t fb = (slot >> 1) - 1;
                price += rtree_price(m->spec[slot], (int)fb, d - ((2 | (slot & 1)) << fb));
            }
            pr->dist_small[ls][d] = price;
        }
    }
    for (uint32_t a = 0; a < 16; a++) pr->align[a] = rtree_price(m->align, 4, a);
}

// d = distance - 1
static inline uint32_t dist_price(const pricer_t *pr, uint32_t d, uint32_t len) {
    uint32_t ls = len - CX_MIN_MATCH;
    if (ls > 3) ls = 3;
    if (d < 128) return pr->dist_small[ls][d];
    uint32_t slot = dist_slot(d);
    uint32_t fb = (slot >> 1) - 1;
    return pr->slot[ls][slot] + ((fb - 4) << 4) + pr->align[d & 15];
}

static inline uint32_t rep_index_price(const model_t *m, uint32_t idx, uint32_t state, uint32_t ps) {
    if (idx == 0) return bit_price(m->is_rep0[state], 0) + bit_price(m->is_rep0_long[state][ps], 1);
    uint32_t price = bit_price(m->is_rep0[state], 1);
    if (idx == 1) return price + bit_price(m->is_rep1[state], 0);
    return price + bit_price(m->is_rep1[state], 1) + bit_price(m->is_rep2[state], idx == 3);
}

static inline void opt_relax(opt_node_t *opt, uint32_t *end, uint32_t from, uint32_t to,
                             uint32_t price, uint8_t op, uint32_t len, uint32_t arg) {
    while (*end < to) opt[++*end].price = PRICE_INF;
    if (price < opt[to].price) {
        opt[to].price = price;
        opt[to].prev = from;
        opt[to].op = op;
        opt[to].len = len;
        opt[to].arg = arg;
    }
}

// The coder state after taking node's packet from its predecessor
static void opt_derive(opt_node_t *node, const opt_node_t *from) {
    node->st = from->st;
    switch (node->op) {
    case OP_LIT:      node->st.state = st_lit(node->st.state); break;
    case OP_SHORTREP: node->st.state = st_short(node->st.state); break;
    case OP_REP:      reps_use(node->st.reps, node->arg); node->st.state = st_rep(node->st.state); break;
    default:          reps_push(node->st.reps, node->arg); node->st.state = st_match(node->st.state); break;
    }
}

static size_t cx_compress_opt(cx_enc_t *e, const uint8_t *in, uint32_t n, uint8_t *out, size_t cap) {
    rc_enc_t rc;
    enc_begin(e, &rc, out, cap);
    model_t *m = &e->model;
    const pricer_t *pr = &e->prices;
    opt_node_t *opt = e->opt;

    cx_state_t s = { 0, { 1, 1, 1, 1 } };
    uint32_t pos = 0, next_refresh = 0;
    uint32_t mlens[CX_MAX_MATCH + 1], mdists[CX_MAX_MATCH + 1];

    while (pos < n) {
        if (rc.overflow) return 0;
        if (pos >= next_refresh) {
            fill_prices(e);
            next_refresh = pos + 2048;
        }

        opt[0].price = 0;
        opt[0].st = s;
        uint32_t end = 0, target = 0;

        for (uint32_t i = 0;; i++) {
            // Every path has converged here, or the look-ahead window is full
            if ((i > 0 && i == end) || i >= OPT_NUM - CX_MAX_MATCH - 1) {
                target = i;
                break;
            }
            opt_node_t *node = &opt[i];
            if (i > 0) opt_derive(node, &opt[node->prev]);

            uint32_t p = pos + i;
            uint32_t state = node->st.state;
            uint32_t ps = p & (CX_POS_STATES - 1);
            uint32_t max_len = n - p;
            if (max_len > CX_MAX_MATCH) max_len = CX_MAX_MATCH;

            opt_relax(opt, &end, i, i + 1,
                      node->price + bit_price(m->is_match[state][ps], 0) + literal_price(m, in, p, &node->st),
                      OP_LIT, 1, 0);

            uint32_t match_base = node->price + bit_price(m->is_match[state][ps], 1);
            uint32_t rep_base = match_base + bit_price(m->is_rep[state], 1);

            uint32_t r0 = node->st.reps[0];
            if (r0 <= p && in[p] == in[p - r0]) {
                opt_relax(opt, &end, i, i + 1,
                          rep_base + bit_price(m->is_rep0[state], 0) + bit_price(m->is_rep0_long[state][ps], 0),
                          OP_SHORTREP, 1, 0);
            }

            uint32_t best_rep = 0;
            if (max_len >= CX_MIN_MATCH) {
                for (uint32_t r = 0; r < 4; r++) {
                    uint32_t d = node->st.reps[r];
                    if (d > p) continue;
                    uint32_t len = 0;
                    while (len < max_len && in[p + len] == in[p + len - d]) len++;
                    if (len < CX_MIN_MATCH) continue;
                    uint32_t base = rep_base + rep_index_price(m, r, state, ps);
                    for (uint32_t l = CX_MIN_MATCH; l <= len; l++) {
                        opt_relax(opt, &end, i, i + l, base + pr->len[1][ps][l], OP_REP, l, r);
                    }
                    if (len > best_rep) best_rep = len;
                }
            }
            if (best_rep >= e->nice) {
                target = i + best_rep;
                break;
            }

            ensure_inserted(e, in, n, p);
            uint32_t count = find_matches(e, in, n, p, mlens, mdists);
            if (count > 0) {
                uint32_t base = match_base + bit_price(m->is_rep[state], 0);
                uint32_t l = 3;
                for (uint32_t k = 0; k < count; k++) {
                    for (; l <= mlens[k]; l++) {
                        opt_relax(opt, &end, i, i + l,
                                  base + pr->len[0][ps][l] + dist_price(pr, mdists[k] - 1, l),
                                  OP_MATCH, l, mdists[k]);
                    }
                }
                if (mlens[count - 1] >= e->nice) {
                    target = i + mlens[count - 1];
                    break;
                }
            }
        }

        // Walk back from the target and emit the chosen packets in order
        uint32_t steps = 0;
        for (uint32_t k = target; k > 0; k = opt[k].prev) e->path[steps++] = k;
        while (steps > 0) {
            const opt_node_t *node = &opt[e->path[--steps]];
            switch (node->op) {
            case OP_LIT:      emit_literal(&rc, m, in, pos, &s); break;
            case OP_SHORTREP: emit_shortrep(&rc, m, pos, &s); break;
            case OP_REP:      emit_rep(&rc, m, pos, &s, node->arg, node->len); break;
            default:          emit_match(&rc, m, pos, &s, node->len, node->arg); break;
            }
            pos += node->len;
        }
    }

    rc_flush(&rc);
    return rc.overflow ? 0 : rc.pos;
}

/* Compresses one block (n <= capacity). Returns the compressed size, or 0 if
 * the result would not fit in cap bytes (the caller stores the block raw). */
static size_t cx_compress(cx_enc_t *e, const uint8_t *in, uint32_t n, uint8_t *out, size_t cap) {
    if (n == 0 || n > e->capacity) return 0;
    return e->optimal ? cx_compress_opt(e, in, n, out, cap) : cx_compress_fast(e, in, n, out, cap);
}

/* ---------- x86 filter ----------
 * x86 CALL instructions (E8 + 32-bit relative offset) to the same function
 * have different bytes at every call site. Turning the offset into an
 * absolute position makes repeated calls identical, so programs and
 * libraries compress much better. The scan never looks at the bytes it
 * rewrites, so it is exactly reversible. */

static void x86_filter(uint8_t *b, uint32_t n, int encode) {
    for (uint32_t i = 0; i + 5 <= n;) {
        if (b[i] == 0xE8) {
            uint32_t v = get_le32(b + i + 1);
            uint32_t next = i + 5;
            put_le32(b + i + 1, encode ? v + next : v - next);
            i += 5;
        } else {
            i++;
        }
    }
}

// CALL opcodes well above the rate random data would have
static int looks_like_x86(const uint8_t *b, uint32_t n) {
    uint32_t calls = 0;
    for (uint32_t i = 0; i < n; i++) calls += (b[i] == 0xE8);
    return calls > n / 128;
}

// Decodes a stored / CX / CX+x86 block. Returns 0, or -1 if corrupt.
static int decode_typed(uint8_t type, const uint8_t *in, uint32_t len, uint8_t *out, uint32_t raw, model_t *model) {
    if (type == BLOCK_STORED) {
        if (len != raw) return -1;
        memcpy(out, in, raw);
        return 0;
    }
    if ((type != BLOCK_CX && type != BLOCK_CX_X86) || len >= raw) return -1;
    if (cx_decompress(in, len, out, raw, model) != 0) return -1;
    if (type == BLOCK_CX_X86) x86_filter(out, raw, 0);
    return 0;
}

/* =====================================================================
 *  Image reading (shared by extract, test, list, info and mount)
 * ===================================================================== */

typedef struct {
    uint8_t version;
    uint8_t level;
    uint32_t block_size;
    uint32_t block_count;
    uint32_t node_count;
    uint32_t block_table_crc;
    uint32_t meta_crc;          // crc32 of the decoded metadata
    uint64_t data_size;         // length of the logical data stream
    uint64_t block_table_off;
    uint64_t meta_off;
    uint64_t meta_stored_len;
    uint64_t meta_raw_len;
    uint64_t original_size;     // total size of all files, duplicates included
    uint64_t image_size;
} header_t;

typedef struct {
    uint64_t offset;
    uint32_t stored_len;
    uint8_t type;
} block_t;

typedef struct {
    const char *path;           // not NUL-terminated, see path_len
    uint32_t path_len;
    uint32_t mode;
    uint32_t uid;
    uint32_t gid;
    int64_t mtime;
    uint32_t mtime_nsec;
    int64_t atime;
    uint32_t atime_nsec;
    uint64_t data_off;          // regular files
    uint64_t size;
    uint32_t crc;
    uint32_t link;              // hard link: index of an earlier regular-file entry, or NO_LINK
    const char *target;         // symlinks, not NUL-terminated
    uint32_t target_len;
    uint64_t rdev;              // device nodes
    uint32_t xattr_count;       // extended attributes (ACLs, capabilities, ...)
    const uint8_t *xattrs;      // first record, walk with xattr_next()
} meta_entry_t;

#define XATTR_NAME_MAX_LEN  255
#define XATTR_VALUE_MAX_LEN 65536

/* Reads one extended-attribute record (already validated by meta_next).
 * Copies the NUL-terminated name into name[XATTR_NAME_MAX_LEN + 1] and
 * returns a pointer to the next record. */
static const uint8_t* xattr_next(const uint8_t *rec, char *name, const uint8_t **value, uint32_t *value_len) {
    uint32_t name_len = get_le32(rec);
    memcpy(name, rec + 4, name_len);
    name[name_len] = '\0';
    rec += 4 + name_len;
    *value_len = get_le32(rec);
    *value = rec + 4;
    return rec + 4 + *value_len;
}

typedef struct {
    int fd;
    header_t h;
    block_t *blocks;
    uint8_t *meta;
} image_t;

// One decoded block, reused while reads stay inside it. One per thread.
typedef struct {
    const image_t *img;
    int64_t index;
    uint8_t *raw;
    uint8_t *scratch;
    model_t *model;
} block_cache_t;

static int pread_full(int fd, void *buf, size_t n, uint64_t off) {
    uint8_t *p = buf;
    while (n > 0) {
        ssize_t r = pread(fd, p, n, (off_t)off);
        if (r < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (r == 0) {
            errno = EIO;
            return -1;
        }
        p += r;
        n -= (size_t)r;
        off += (uint64_t)r;
    }
    return 0;
}

static int write_all(int fd, const void *buf, size_t n) {
    const uint8_t *p = buf;
    while (n > 0) {
        ssize_t w = write(fd, p, n);
        if (w < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        p += w;
        n -= (size_t)w;
    }
    return 0;
}

static void header_encode(const header_t *h, uint8_t out[HEADER_SIZE]) {
    memset(out, 0, HEADER_SIZE);
    memcpy(out, MAGIC, 4);
    out[4] = h->version;
    out[5] = h->level;
    put_le32(out + 8, h->block_size);
    put_le32(out + 12, h->block_count);
    put_le32(out + 16, h->node_count);
    put_le32(out + 20, h->block_table_crc);
    put_le32(out + 24, h->meta_crc);
    put_le64(out + 32, h->data_size);
    put_le64(out + 40, h->block_table_off);
    put_le64(out + 48, h->meta_off);
    put_le64(out + 56, h->meta_stored_len);
    put_le64(out + 64, h->meta_raw_len);
    put_le64(out + 72, h->original_size);
    put_le64(out + 80, h->image_size);
    put_le32(out + 92, crc32_update(0, out, 92));
}

static int header_decode(const uint8_t *in, header_t *h, char *err, size_t err_len) {
    if (memcmp(in, MAGIC, 4) != 0) {
        snprintf(err, err_len, "not a Claudex image");
        return -1;
    }
    if (in[4] != FORMAT_VERSION) {
        snprintf(err, err_len, "image format version %u is not supported (this build reads version %u) - recreate the image",
                 in[4], FORMAT_VERSION);
        return -1;
    }
    if (crc32_update(0, in, 92) != get_le32(in + 92)) {
        snprintf(err, err_len, "image header is corrupt");
        return -1;
    }
    memset(h, 0, sizeof(*h));
    h->version = in[4];
    h->level = in[5];
    h->block_size = get_le32(in + 8);
    h->block_count = get_le32(in + 12);
    h->node_count = get_le32(in + 16);
    h->block_table_crc = get_le32(in + 20);
    h->meta_crc = get_le32(in + 24);
    h->data_size = get_le64(in + 32);
    h->block_table_off = get_le64(in + 40);
    h->meta_off = get_le64(in + 48);
    h->meta_stored_len = get_le64(in + 56);
    h->meta_raw_len = get_le64(in + 64);
    h->original_size = get_le64(in + 72);
    h->image_size = get_le64(in + 80);
    return 0;
}

static uint32_t block_raw_len(const image_t *img, uint32_t index) {
    if (index + 1 < img->h.block_count) return img->h.block_size;
    return (uint32_t)(img->h.data_size - (uint64_t)index * img->h.block_size);
}

static int meta_next(const image_t *img, size_t *pos, meta_entry_t *e) {
    const uint8_t *m = img->meta;
    size_t len = (size_t)img->h.meta_raw_len;
    size_t p = *pos;
    if (p == len) return 0;

#define NEED(n) do { if (len - p < (size_t)(n)) return -1; } while (0)
    memset(e, 0, sizeof(*e));
    NEED(4);
    e->path_len = get_le32(m + p);
    p += 4;
    if (e->path_len >= MAX_PATH_LEN) return -1;
    NEED(e->path_len);
    e->path = (const char*)m + p;
    if (memchr(e->path, '\0', e->path_len) != NULL) return -1;
    p += e->path_len;

    NEED(36);
    e->mode = get_le32(m + p);
    e->uid = get_le32(m + p + 4);
    e->gid = get_le32(m + p + 8);
    e->mtime = (int64_t)get_le64(m + p + 12);
    e->mtime_nsec = get_le32(m + p + 20);
    e->atime = (int64_t)get_le64(m + p + 24);
    e->atime_nsec = get_le32(m + p + 32);
    p += 36;
    if (e->mtime_nsec >= 1000000000u || e->atime_nsec >= 1000000000u) return -1;

    e->link = NO_LINK;
    if (S_ISREG(e->mode)) {
        NEED(24);
        e->data_off = get_le64(m + p);
        e->size = get_le64(m + p + 8);
        e->crc = get_le32(m + p + 16);
        e->link = get_le32(m + p + 20);
        p += 24;
        if (e->size > img->h.data_size || e->data_off > img->h.data_size - e->size) return -1;
    } else if (S_ISLNK(e->mode)) {
        NEED(4);
        e->target_len = get_le32(m + p);
        p += 4;
        if (e->target_len >= MAX_PATH_LEN) return -1;
        NEED(e->target_len);
        e->target = (const char*)m + p;
        if (memchr(e->target, '\0', e->target_len) != NULL) return -1;
        p += e->target_len;
    } else if (!S_ISDIR(e->mode)) {
        NEED(8);
        e->rdev = get_le64(m + p);
        p += 8;
    }

    NEED(4);
    e->xattr_count = get_le32(m + p);
    p += 4;
    e->xattrs = m + p;
    for (uint32_t i = 0; i < e->xattr_count; i++) {
        NEED(4);
        uint32_t name_len = get_le32(m + p);
        p += 4;
        if (name_len == 0 || name_len > XATTR_NAME_MAX_LEN) return -1;
        NEED(name_len);
        if (memchr(m + p, '\0', name_len) != NULL) return -1;
        p += name_len;
        NEED(4);
        uint32_t value_len = get_le32(m + p);
        p += 4;
        if (value_len > XATTR_VALUE_MAX_LEN) return -1;
        NEED(value_len);
        p += value_len;
    }
#undef NEED

    *pos = p;
    return 1;
}

static void image_close(image_t *img) {
    if (img->fd >= 0) close(img->fd);
    free(img->blocks);
    free(img->meta);
    img->fd = -1;
    img->blocks = NULL;
    img->meta = NULL;
}

// Decodes the chunked metadata region into img->meta
static int decode_metadata(image_t *img, const uint8_t *stored, uint64_t stored_len) {
    model_t *model = malloc(sizeof(model_t));
    if (!model) return -1;
    uint64_t in = 0, out = 0;
    int rc = 0;
    while (out < img->h.meta_raw_len) {
        if (stored_len - in < CHUNK_HEADER_SIZE) { rc = -1; break; }
        uint32_t raw = get_le32(stored + in);
        uint32_t len = get_le32(stored + in + 4);
        uint8_t type = stored[in + 8];
        in += CHUNK_HEADER_SIZE;
        if (raw == 0 || raw > MAX_BLOCK_SIZE || raw > img->h.meta_raw_len - out || len > stored_len - in ||
            decode_typed(type, stored + in, len, img->meta + out, raw, model) != 0) {
            rc = -1;
            break;
        }
        in += len;
        out += raw;
    }
    if (in != stored_len) rc = -1;
    free(model);
    return rc;
}

// Opens and fully validates an image: header, block table, metadata, footer
static int image_open(image_t *img, const char *path, char *err, size_t err_len) {
    memset(img, 0, sizeof(*img));
    img->fd = open(path, O_RDONLY | O_CLOEXEC);
    if (img->fd < 0) {
        snprintf(err, err_len, "cannot open %s: %s", path, strerror(errno));
        return -1;
    }

    header_t *h = &img->h;
    uint8_t hb[HEADER_SIZE];
    struct stat st;
    uint8_t *tb = NULL;
    uint8_t *stored = NULL;

    if (fstat(img->fd, &st) != 0 || pread_full(img->fd, hb, HEADER_SIZE, 0) != 0) {
        snprintf(err, err_len, "not a Claudex image (too small)");
        goto fail;
    }
    if (header_decode(hb, h, err, err_len) != 0) goto fail;

    if ((uint64_t)st.st_size != h->image_size) {
        snprintf(err, err_len, "image is %" PRIu64 " bytes but should be %" PRIu64 " (truncated or incomplete)",
                 (uint64_t)st.st_size, h->image_size);
        goto fail;
    }

    uint64_t table_len = (uint64_t)h->block_count * BLOCK_ENTRY_SIZE;
    if (h->block_size < MIN_BLOCK_SIZE || h->block_size > MAX_BLOCK_SIZE ||
        (h->data_size + h->block_size - 1) / h->block_size != h->block_count ||
        h->block_table_off < HEADER_SIZE || h->block_table_off > h->image_size ||
        table_len > h->image_size - h->block_table_off ||
        h->meta_off != h->block_table_off + table_len ||
        h->meta_stored_len > h->image_size - h->meta_off ||
        h->image_size - h->meta_off - h->meta_stored_len != FOOTER_SIZE ||
        h->meta_raw_len > MAX_META_SIZE) {
        snprintf(err, err_len, "image layout is corrupt");
        goto fail;
    }

    // Block table
    tb = malloc(table_len ? table_len : 1);
    img->blocks = calloc(h->block_count ? h->block_count : 1, sizeof(block_t));
    if (!tb || !img->blocks) {
        snprintf(err, err_len, "out of memory");
        goto fail;
    }
    if (pread_full(img->fd, tb, table_len, h->block_table_off) != 0 ||
        crc32_update(0, tb, table_len) != h->block_table_crc) {
        snprintf(err, err_len, "block table is corrupt");
        goto fail;
    }
    uint64_t expect_off = HEADER_SIZE;
    for (uint32_t i = 0; i < h->block_count; i++) {
        block_t *b = &img->blocks[i];
        const uint8_t *e = tb + (uint64_t)i * BLOCK_ENTRY_SIZE;
        b->offset = get_le64(e);
        b->stored_len = get_le32(e + 8);
        b->type = e[12];
        uint32_t raw = block_raw_len(img, i);
        int ok = (b->offset == expect_off) &&
                 ((b->type == BLOCK_STORED && b->stored_len == raw) ||
                  ((b->type == BLOCK_CX || b->type == BLOCK_CX_X86) && b->stored_len >= 5 && b->stored_len < raw));
        if (!ok) {
            snprintf(err, err_len, "block table is corrupt (block %u)", i);
            goto fail;
        }
        expect_off += b->stored_len;
    }
    if (expect_off != h->block_table_off) {
        snprintf(err, err_len, "block table is corrupt");
        goto fail;
    }
    free(tb);
    tb = NULL;

    // Metadata
    stored = malloc(h->meta_stored_len ? h->meta_stored_len : 1);
    img->meta = malloc(h->meta_raw_len ? h->meta_raw_len : 1);
    if (!stored || !img->meta) {
        snprintf(err, err_len, "out of memory");
        goto fail;
    }
    if (pread_full(img->fd, stored, h->meta_stored_len, h->meta_off) != 0 ||
        decode_metadata(img, stored, h->meta_stored_len) != 0 ||
        crc32_update(0, img->meta, h->meta_raw_len) != h->meta_crc) {
        snprintf(err, err_len, "metadata is corrupt");
        goto fail;
    }
    free(stored);
    stored = NULL;

    // Footer
    uint8_t footer[FOOTER_SIZE];
    if (pread_full(img->fd, footer, FOOTER_SIZE, h->meta_off + h->meta_stored_len) != 0 ||
        memcmp(footer, FOOTER_MAGIC, 4) != 0 || get_le32(footer + 4) != h->node_count) {
        snprintf(err, err_len, "image footer is corrupt");
        goto fail;
    }

    // Walk the metadata once so later users can trust it. A hard link must
    // point at an earlier regular file that is not itself a link.
    size_t pos = 0;
    uint32_t count = 0;
    meta_entry_t e;
    int r;
    uint8_t *is_target = calloc(h->node_count ? h->node_count : 1, 1);
    if (!is_target) {
        snprintf(err, err_len, "out of memory");
        goto fail;
    }
    while ((r = meta_next(img, &pos, &e)) == 1) {
        if (count >= h->node_count) break;
        if (e.link != NO_LINK && (e.link >= count || !is_target[e.link])) {
            r = -1;
            break;
        }
        is_target[count] = S_ISREG(e.mode) && e.link == NO_LINK;
        count++;
    }
    free(is_target);
    if (r != 0 || count != h->node_count) {
        snprintf(err, err_len, "metadata is corrupt");
        goto fail;
    }
    return 0;

fail:
    free(tb);
    free(stored);
    image_close(img);
    return -1;
}

static int read_block(const image_t *img, uint32_t index, uint8_t *out, uint8_t *scratch, model_t *model) {
    const block_t *b = &img->blocks[index];
    uint32_t raw = block_raw_len(img, index);
    if (b->type == BLOCK_STORED) return pread_full(img->fd, out, raw, b->offset);
    if (pread_full(img->fd, scratch, b->stored_len, b->offset) != 0) return -1;
    return decode_typed(b->type, scratch, b->stored_len, out, raw, model);
}

static int cache_init(block_cache_t *c, const image_t *img) {
    c->img = img;
    c->index = -1;
    c->raw = malloc(img->h.block_size);
    c->scratch = malloc(img->h.block_size);
    c->model = malloc(sizeof(model_t));
    return (c->raw && c->scratch && c->model) ? 0 : -1;
}

static void cache_free(block_cache_t *c) {
    free(c->raw);
    free(c->scratch);
    free(c->model);
}

// Copies len bytes of the data stream starting at off. Returns 0, or -1 on a corrupt block.
static int read_stream(block_cache_t *c, uint64_t off, uint8_t *buf, size_t len) {
    uint32_t bs = c->img->h.block_size;
    while (len > 0) {
        uint32_t index = (uint32_t)(off / bs);
        uint32_t in_block = (uint32_t)(off % bs);
        if (c->index != (int64_t)index) {
            if (read_block(c->img, index, c->raw, c->scratch, c->model) != 0) {
                c->index = -1;
                return -1;
            }
            c->index = index;
        }
        size_t n = block_raw_len(c->img, index) - in_block;
        if (n > len) n = len;
        memcpy(buf, c->raw + in_block, n);
        buf += n;
        off += n;
        len -= n;
    }
    return 0;
}

// Relative, no "", "." or ".." components: nothing can escape the destination
static int safe_rel_path(const char *p) {
    if (p[0] == '\0') return 1;
    if (p[0] == '/') return 0;
    const char *s = p;
    for (;;) {
        const char *slash = strchr(s, '/');
        size_t len = slash ? (size_t)(slash - s) : strlen(s);
        if (len == 0) return 0;
        if (len == 1 && s[0] == '.') return 0;
        if (len == 2 && s[0] == '.' && s[1] == '.') return 0;
        if (!slash) return 1;
        s = slash + 1;
    }
}

static void format_size(uint64_t size, char *buf, size_t buf_size) {
    if (size >= 1073741824) snprintf(buf, buf_size, "%.2f GiB", size / 1073741824.0);
    else if (size >= 1048576) snprintf(buf, buf_size, "%.2f MiB", size / 1048576.0);
    else if (size >= 1024) snprintf(buf, buf_size, "%.2f KiB", size / 1024.0);
    else snprintf(buf, buf_size, "%" PRIu64 " B", size);
}

static void join_path(char *out, size_t out_size, const char *dir, const char *name, int *too_long) {
    int n;
    if (name[0] == '\0') n = snprintf(out, out_size, "%s", dir);
    else if (dir[0] == '\0') n = snprintf(out, out_size, "%s", name);
    else if (strcmp(dir, "/") == 0) n = snprintf(out, out_size, "/%s", name);
    else n = snprintf(out, out_size, "%s/%s", dir, name);
    if (too_long) *too_long = (n < 0 || (size_t)n >= out_size);
}

// mkdir -p: create every missing folder along path. Returns 0 or -1 (errno set).
static int mkdir_p(const char *path, mode_t mode) {
    char buf[MAX_PATH_LEN];
    if (snprintf(buf, sizeof(buf), "%s", path) >= (int)sizeof(buf)) {
        errno = ENAMETOOLONG;
        return -1;
    }
    if (buf[0] == '\0') return 0;
    for (char *s = buf + 1;; s++) {
        if (*s == '/' || *s == '\0') {
            char c = *s;
            *s = '\0';
            struct stat st;
            if (stat(buf, &st) != 0) {
                if (mkdir(buf, mode) != 0 && errno != EEXIST) return -1;
                if (stat(buf, &st) != 0) return -1;
            }
            if (!S_ISDIR(st.st_mode)) {
                errno = ENOTDIR;
                return -1;
            }
            if (c == '\0') return 0;
            *s = c;
        }
    }
}

// mkdir -p for the folder that will contain path
static int mkdir_parent(const char *path, mode_t mode) {
    char buf[MAX_PATH_LEN];
    snprintf(buf, sizeof(buf), "%s", path);
    char *slash = strrchr(buf, '/');
    if (!slash || slash == buf) return 0;   // current folder or /
    *slash = '\0';
    return mkdir_p(buf, mode);
}

/* =====================================================================
 *  create
 * ===================================================================== */

// Always excluded unless --no-default-excludes: virtual/kernel filesystems,
// temporary data, mount points, swap, caches and logs (only when they lie
// inside the source). Entries with * are patterns.
static const char *default_excludes[] = {
    "/proc", "/sys", "/dev", "/run", "/tmp", "/var/tmp",
    "/mnt", "/media", "/lost+found", "/swapfile", "/swap.img",
    "/var/cache/pacman/pkg", "/var/log/journal", "/var/lib/systemd/coredump",
    "/home/*/.cache", "/root/.cache",
    "/etc/fstab",
    NULL
};

// Entries with these names are skipped wherever they appear
static const char *default_exclude_names[] = {
    "root.claudex",
    "backup.claudex",
    NULL
};

static const char spinner_chars[] = "|/-\\";

typedef struct {
    char *rel_path;
    uint64_t size;          // from stat; after packing, the bytes actually stored
    uint64_t data_off;
    uint64_t rdev;
    int64_t mtime, atime;
    uint32_t mtime_nsec, atime_nsec;
    uint32_t mode, uid, gid;
    uint32_t crc;
    uint32_t dup_of;        // entry index of an identical file, or NO_DUP
    uint32_t pre_crc;       // checksum from the duplicate scan
    uint32_t link_to;       // entry index of the first name of this hard-linked file, or NO_LINK
    uint64_t dev, ino;      // identity, to find hard links
    uint8_t multi_link;     // st_nlink > 1
    uint8_t pre_ok;
    uint8_t skipped;
} entry_t;

typedef struct {
    char **paths;
    uint32_t count;
} exclude_list_t;

enum { SLOT_FREE, SLOT_FILLING, SLOT_PENDING, SLOT_BUSY, SLOT_DONE };

typedef struct {
    int state;
    uint8_t *in;
    uint32_t in_len;
    uint8_t *out;
    uint32_t out_len;
    uint8_t type;
} slot_t;

typedef struct {
    uint8_t *p;
    size_t len;
    size_t cap;
    int error;
} buf_t;

typedef struct packer {
    // options
    char source_root[MAX_PATH_LEN];
    int level;
    uint32_t block_size;
    int threads;
    int dedup;
    int default_excludes_on;
    int show_progress;
    exclude_list_t excludes;
    dev_t output_dev;
    ino_t output_ino;
    int out_fd;
    char output_name[1024];
    time_t start_time;

    entry_t *entries;
    uint32_t entry_count;
    uint32_t entry_cap;
    uint32_t *order;            // regular files, in data stream order
    uint32_t order_count;

    // pipeline, protected by mutex
    slot_t *slots;
    uint32_t nslots;
    uint64_t produced;
    uint64_t next_compress;
    uint64_t next_write;
    int producer_done;
    pthread_cond_t cond_free;
    pthread_cond_t cond_pending;
    pthread_cond_t cond_done;

    // writer (main thread) only
    block_t *table;
    uint32_t table_count;
    uint32_t table_cap;
    uint64_t out_pos;
    int io_error;
    int io_errno;
    uint64_t stream_size;       // set by the producer when it finishes

    // statistics, protected by mutex
    uint64_t total_source_size;
    uint64_t current_output_size;
    uint64_t current_cloned_size;
    uint64_t dedup_saved;
    uint32_t dedup_files;
    uint32_t warnings;
    int progress_running;
    buf_t deferred;             // warnings held back while the progress line is showing

    pthread_mutex_t mutex;
    pthread_t progress_thread;
} packer_t;

typedef struct {
    packer_t *p;
    cx_enc_t *enc;
    model_t *model;
    uint8_t *check;
    uint8_t *filt;          // block copy for the x86 filter
} cworker_t;

static void buf_put(buf_t *b, const void *data, size_t n) {
    if (b->error || n == 0) return;
    if (b->len + n > b->cap) {
        size_t cap = b->cap ? b->cap : 65536;
        while (cap < b->len + n) cap *= 2;
        uint8_t *q = realloc(b->p, cap);
        if (!q) {
            b->error = 1;
            return;
        }
        b->p = q;
        b->cap = cap;
    }
    memcpy(b->p + b->len, data, n);
    b->len += n;
}

static void buf_u32(buf_t *b, uint32_t v) {
    uint8_t t[4];
    put_le32(t, v);
    buf_put(b, t, 4);
}

static void buf_u64(buf_t *b, uint64_t v) {
    uint8_t t[8];
    put_le64(t, v);
    buf_put(b, t, 8);
}

static void warnf(packer_t *p, const char *fmt, ...) __attribute__((format(printf, 2, 3)));

static void warnf(packer_t *p, const char *fmt, ...) {
    char msg[MAX_PATH_LEN + 256];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof(msg), fmt, ap);
    va_end(ap);

    pthread_mutex_lock(&p->mutex);
    p->warnings++;
    if (p->progress_running) {
        // Printing now would push the progress line down; show it afterwards
        buf_put(&p->deferred, msg, strlen(msg));
        buf_put(&p->deferred, "\n", 1);
    } else {
        fprintf(stderr, "\033[33mWarning: %s\033[0m\n", msg);
    }
    pthread_mutex_unlock(&p->mutex);
}

/* ---------- terminal handling for the progress line ---------- */

static volatile sig_atomic_t g_term_dirty;
static char g_partial_output[MAX_PATH_LEN];

static void restore_terminal(void) {
    if (g_term_dirty) {
        // re-enable line wrap, show the cursor
        const char s[] = "\033[?7h\033[?25h";
        if (write(STDOUT_FILENO, s, sizeof(s) - 1) < 0) { /* nothing to do */ }
        g_term_dirty = 0;
    }
}

static void on_signal(int sig) {
    restore_terminal();
    if (write(STDOUT_FILENO, "\n", 1) < 0) { /* nothing to do */ }
    if (g_partial_output[0]) unlink(g_partial_output);
    signal(sig, SIG_DFL);
    raise(sig);
}

static int term_columns(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0) return ws.ws_col;
    return 80;
}

// Draws the whole progress line in one write. Caller holds p->mutex.
static void draw_progress(packer_t *p, float percentage) {
    static int spinner_idx = 0;
    if (percentage > 100.0f) percentage = 100.0f;
    if (percentage < 0.0f) percentage = 0.0f;
    char spin_char = spinner_chars[spinner_idx++ % 4];

    time_t elapsed = time(NULL) - p->start_time;
    int hours = elapsed / 3600;
    int mins = (elapsed % 3600) / 60;
    int secs = elapsed % 60;

    char out_str[32], cloned_str[32], total_str[32];
    format_size(p->current_output_size, out_str, sizeof(out_str));
    format_size(p->current_cloned_size, cloned_str, sizeof(cloned_str));
    format_size(p->total_source_size, total_str, sizeof(total_str));

    // Visible widths of each part, to fit the line inside the terminal
    char pct_txt[16], name_txt[1100], cloned_txt[96], time_txt[48];
    int pct_w = snprintf(pct_txt, sizeof(pct_txt), " %3.0f%%", percentage);
    int name_w = snprintf(name_txt, sizeof(name_txt), "  %s: %s", p->output_name, out_str);
    int cloned_w = snprintf(cloned_txt, sizeof(cloned_txt), "  Cloned: %s / %s", cloned_str, total_str);
    int time_w = snprintf(time_txt, sizeof(time_txt), "  Time: %02d:%02d:%02d", hours, mins, secs);

    int cols = term_columns() - 1;      // never write into the last column
    int show_name = 1, show_cloned = 1, show_time = 1;
    int bar_width = cols - 2 - pct_w - name_w - cloned_w - time_w;
    if (bar_width < 10) { show_name = 0; bar_width += name_w; }
    if (bar_width < 10) { show_cloned = 0; bar_width += cloned_w; }
    if (bar_width < 10) { show_time = 0; bar_width += time_w; }
    if (bar_width > 50) bar_width = 50;
    if (bar_width < 1) bar_width = 1;
    int filled = (int)(percentage * bar_width / 100);

    char line[2048];
    size_t n = 0;
#define ADD(...) do { if (n < sizeof(line)) n += (size_t)snprintf(line + n, sizeof(line) - n, __VA_ARGS__); } while (0)
    ADD("\r\033[32m[\033[0m");
    // Progress bar with the spinner in the first cell
    if (filled > 0) {
        ADD("\033[42m%c", spin_char);
        for (int i = 1; i < filled; i++) ADD(" ");
        ADD("\033[0m");
    } else {
        ADD("\033[32m%c\033[0m", spin_char);
    }
    for (int i = filled > 0 ? filled : 1; i < bar_width; i++) ADD(" ");
    ADD("\033[32m]\033[0m\033[32m%s\033[0m", pct_txt);
    if (show_name) ADD("  \033[36m%s:\033[0m \033[32m%s\033[0m", p->output_name, out_str);
    if (show_cloned) ADD("  \033[36mCloned:\033[0m \033[32m%s / %s\033[0m", cloned_str, total_str);
    if (show_time) ADD("  \033[36mTime:\033[0m \033[32m%02d:%02d:%02d\033[0m", hours, mins, secs);
    ADD("\033[K");
#undef ADD
    if (n >= sizeof(line)) n = sizeof(line) - 1;
    fwrite(line, 1, n, stdout);
    fflush(stdout);
}

static void* progress_thread(void *arg) {
    packer_t *p = arg;
    for (;;) {
        pthread_mutex_lock(&p->mutex);
        if (!p->progress_running) {
            pthread_mutex_unlock(&p->mutex);
            break;
        }
        float pct = p->total_source_size ? (p->current_cloned_size * 100.0f) / p->total_source_size : 0.0f;
        draw_progress(p, pct);
        pthread_mutex_unlock(&p->mutex);
        usleep(100000);
    }
    return NULL;
}

/* ---------- excludes and scanning ---------- */

static void strip_trailing_slashes(char *s) {
    size_t len = strlen(s);
    while (len > 1 && s[len - 1] == '/') s[--len] = '\0';
}

static int is_pattern(const char *s) {
    return strpbrk(s, "*?[") != NULL;
}

static void add_exclude_path(exclude_list_t *list, const char *path) {
    char **paths = realloc(list->paths, (list->count + 1) * sizeof(char*));
    if (!paths) return;
    list->paths = paths;
    // Resolve to an absolute path so it matches however the source was given
    char *copy = is_pattern(path) ? NULL : realpath(path, NULL);
    if (!copy && path[0] != '/') {
        // Relative path that doesn't exist (yet): anchor it to the current folder
        char cwd[MAX_PATH_LEN], abs[MAX_PATH_LEN * 2];
        if (getcwd(cwd, sizeof(cwd))) {
            const char *rel = (path[0] == '.' && path[1] == '/') ? path + 2 : path;
            snprintf(abs, sizeof(abs), "%s/%s", strcmp(cwd, "/") == 0 ? "" : cwd, rel);
            copy = strdup(abs);
        }
    }
    if (!copy) copy = strdup(path);
    if (!copy) return;
    strip_trailing_slashes(copy);
    list->paths[list->count++] = copy;
}

static int path_is_under(const char *path, const char *prefix) {
    size_t n = strlen(prefix);
    return strncmp(path, prefix, n) == 0 && (path[n] == '/' || path[n] == '\0');
}

static int is_excluded(const exclude_list_t *list, const char *path) {
    for (uint32_t i = 0; i < list->count; i++) {
        const char *x = list->paths[i];
        if (is_pattern(x) ? fnmatch(x, path, FNM_PATHNAME) == 0 : path_is_under(path, x)) return 1;
    }
    return 0;
}

static int is_default_excluded_name(const char *name) {
    for (int i = 0; default_exclude_names[i]; i++) {
        if (strcmp(name, default_exclude_names[i]) == 0) return 1;
    }
    return 0;
}

static int add_entry(packer_t *p, const char *rel_path, const struct stat *st) {
    if (p->entry_count >= UINT32_MAX - 1) return -1;
    if (p->entry_count == p->entry_cap) {
        uint32_t cap = p->entry_cap ? p->entry_cap * 2 : 1024;
        entry_t *e = realloc(p->entries, (size_t)cap * sizeof(entry_t));
        if (!e) return -1;
        p->entries = e;
        p->entry_cap = cap;
    }
    entry_t *e = &p->entries[p->entry_count];
    memset(e, 0, sizeof(*e));
    e->rel_path = strdup(rel_path);
    if (!e->rel_path) return -1;
    e->mode = st->st_mode;
    e->uid = st->st_uid;
    e->gid = st->st_gid;
    e->mtime = st->st_mtim.tv_sec;
    e->mtime_nsec = (uint32_t)st->st_mtim.tv_nsec;
    e->atime = st->st_atim.tv_sec;
    e->atime_nsec = (uint32_t)st->st_atim.tv_nsec;
    e->rdev = st->st_rdev;
    e->size = S_ISREG(st->st_mode) ? (uint64_t)st->st_size : 0;
    e->dup_of = NO_DUP;
    e->link_to = NO_LINK;
    e->dev = (uint64_t)st->st_dev;
    e->ino = (uint64_t)st->st_ino;
    e->multi_link = S_ISREG(st->st_mode) && st->st_nlink > 1;
    p->entry_count++;
    if (S_ISREG(st->st_mode)) p->total_source_size += e->size;
    return 0;
}

static int traverse_directory(packer_t *p, const char *full, const char *rel) {
    DIR *dir = opendir(full);
    if (!dir) {
        warnf(p, "cannot open directory %s: %s", full, strerror(errno));
        return 0;
    }

    char *child_full = malloc(MAX_PATH_LEN);
    char *child_rel = malloc(MAX_PATH_LEN);
    if (!child_full || !child_rel) {
        free(child_full);
        free(child_rel);
        closedir(dir);
        return -1;
    }

    int rc = 0;
    struct dirent *de;
    while ((de = readdir(dir)) != NULL) {
        if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0) continue;

        int long1, long2;
        join_path(child_full, MAX_PATH_LEN, full, de->d_name, &long1);
        join_path(child_rel, MAX_PATH_LEN, rel, de->d_name, &long2);
        if (long1 || long2) {
            warnf(p, "path too long, skipped: %s/%s", full, de->d_name);
            continue;
        }

        if (is_excluded(&p->excludes, child_full) ||
            (p->default_excludes_on && is_default_excluded_name(de->d_name))) {
            printf("\033[32mExcluding: %s\033[0m\n", child_full);
            continue;
        }

        struct stat st;
        if (lstat(child_full, &st) != 0) {
            warnf(p, "cannot stat %s: %s", child_full, strerror(errno));
            continue;
        }

        // Never pack the image into itself
        if (st.st_dev == p->output_dev && st.st_ino == p->output_ino) continue;

        if (add_entry(p, child_rel, &st) != 0) {
            rc = -1;
            break;
        }
        if (S_ISDIR(st.st_mode) && traverse_directory(p, child_full, child_rel) != 0) {
            rc = -1;
            break;
        }
    }

    free(child_full);
    free(child_rel);
    closedir(dir);
    return rc;
}

/* ---------- data stream order and duplicates ---------- */

static packer_t *g_sort;

static const char* base_name(const char *path) {
    const char *s = strrchr(path, '/');
    return s ? s + 1 : path;
}

static const char* extension(const char *base) {
    const char *d = strrchr(base, '.');
    return (d && d != base) ? d + 1 : "";
}

// Group similar files so they share compression context: by extension, then name, then path
static int cmp_stream_order(const void *a, const void *b) {
    const entry_t *x = &g_sort->entries[*(const uint32_t*)a];
    const entry_t *y = &g_sort->entries[*(const uint32_t*)b];
    const char *bx = base_name(x->rel_path), *by = base_name(y->rel_path);
    int c = strcmp(extension(bx), extension(by));
    if (c) return c;
    c = strcmp(bx, by);
    if (c) return c;
    return strcmp(x->rel_path, y->rel_path);
}

static int cmp_inode(const void *a, const void *b) {
    uint32_t ia = *(const uint32_t*)a, ib = *(const uint32_t*)b;
    const entry_t *x = &g_sort->entries[ia];
    const entry_t *y = &g_sort->entries[ib];
    if (x->dev != y->dev) return x->dev < y->dev ? -1 : 1;
    if (x->ino != y->ino) return x->ino < y->ino ? -1 : 1;
    return ia < ib ? -1 : (ia > ib);
}

// Names that are hard links to the same file: store the data once and
// restore them as hard links. The first name in scan order owns the data.
static void find_hard_links(packer_t *p) {
    uint32_t *idx = malloc((size_t)(p->entry_count ? p->entry_count : 1) * sizeof(uint32_t));
    if (!idx) return;
    uint32_t n = 0;
    for (uint32_t i = 0; i < p->entry_count; i++) {
        if (p->entries[i].multi_link) idx[n++] = i;
    }
    g_sort = p;
    qsort(idx, n, sizeof(uint32_t), cmp_inode);
    for (uint32_t i = 0; i < n;) {
        entry_t *first = &p->entries[idx[i]];
        uint32_t j = i + 1;
        while (j < n && p->entries[idx[j]].dev == first->dev && p->entries[idx[j]].ino == first->ino) {
            entry_t *e = &p->entries[idx[j]];
            e->link_to = idx[i];
            p->total_source_size -= e->size;   // never read twice
            j++;
        }
        i = j;
    }
    free(idx);
}

// a and b are ranks (positions in p->order)
static int cmp_size_rank(const void *a, const void *b) {
    uint32_t ra = *(const uint32_t*)a, rb = *(const uint32_t*)b;
    uint64_t sa = g_sort->entries[g_sort->order[ra]].size;
    uint64_t sb = g_sort->entries[g_sort->order[rb]].size;
    if (sa != sb) return sa < sb ? -1 : 1;
    return ra < rb ? -1 : (ra > rb);
}

static int cmp_hash_rank(const void *a, const void *b) {
    uint32_t ra = *(const uint32_t*)a, rb = *(const uint32_t*)b;
    const entry_t *x = &g_sort->entries[g_sort->order[ra]];
    const entry_t *y = &g_sort->entries[g_sort->order[rb]];
    if (x->pre_ok != y->pre_ok) return x->pre_ok > y->pre_ok ? -1 : 1;
    if (x->size != y->size) return x->size < y->size ? -1 : 1;
    if (x->pre_crc != y->pre_crc) return x->pre_crc < y->pre_crc ? -1 : 1;
    return ra < rb ? -1 : (ra > rb);
}

static int open_regular(const char *path) {
    // O_NOATIME keeps a backup from touching access times (only allowed for the owner/root)
    int fd = open(path, O_RDONLY | O_NONBLOCK | O_NOFOLLOW | O_CLOEXEC | O_NOATIME);
    if (fd < 0 && errno == EPERM) fd = open(path, O_RDONLY | O_NONBLOCK | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return -1;
    // O_NONBLOCK + fstat: don't hang if the file was swapped for a FIFO since the scan
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        close(fd);
        errno = EINVAL;
        return -1;
    }
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
    return fd;
}

static void source_path(const packer_t *p, const entry_t *e, char *out, size_t out_size) {
    join_path(out, out_size, p->source_root, e->rel_path, NULL);
}

typedef struct {
    packer_t *p;
    uint32_t *ranks;
    uint32_t count;
    uint32_t next;
    pthread_mutex_t lock;
} hash_job_t;

static void* hash_worker(void *arg) {
    hash_job_t *job = arg;
    packer_t *p = job->p;
    uint8_t *buf = malloc(1 << 20);
    if (!buf) return NULL;
    char path[MAX_PATH_LEN];

    for (;;) {
        pthread_mutex_lock(&job->lock);
        uint32_t i = job->next++;
        pthread_mutex_unlock(&job->lock);
        if (i >= job->count) break;

        entry_t *e = &p->entries[p->order[job->ranks[i]]];
        source_path(p, e, path, sizeof(path));
        int fd = open_regular(path);
        if (fd < 0) continue;
        uint32_t crc = 0;
        uint64_t total = 0;
        ssize_t n;
        while ((n = read(fd, buf, 1 << 20)) != 0) {
            if (n < 0) {
                if (errno == EINTR) continue;
                break;
            }
            crc = crc32_update(crc, buf, (size_t)n);
            total += (uint64_t)n;
        }
        close(fd);
        if (n == 0 && total == e->size) {
            e->pre_crc = crc;
            e->pre_ok = 1;
        }
    }
    free(buf);
    return NULL;
}

static size_t read_full_fd(int fd, uint8_t *buf, size_t want) {
    size_t got = 0;
    while (got < want) {
        ssize_t r = read(fd, buf + got, want - got);
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) break;
        got += (size_t)r;
    }
    return got;
}

static int files_equal(const packer_t *p, const entry_t *a, const entry_t *b, uint8_t *ba, uint8_t *bb) {
    char pa[MAX_PATH_LEN], pb[MAX_PATH_LEN];
    source_path(p, a, pa, sizeof(pa));
    source_path(p, b, pb, sizeof(pb));
    int fa = open_regular(pa);
    int fb = open_regular(pb);
    int equal = (fa >= 0 && fb >= 0);
    while (equal) {
        size_t na = read_full_fd(fa, ba, 1 << 20);
        size_t nb = read_full_fd(fb, bb, 1 << 20);
        if (na != nb || memcmp(ba, bb, na) != 0) equal = 0;
        if (na == 0 || na != nb) break;
    }
    if (fa >= 0) close(fa);
    if (fb >= 0) close(fb);
    return equal;
}

static void find_duplicates(packer_t *p) {
    uint32_t *ranks = malloc((size_t)(p->order_count ? p->order_count : 1) * sizeof(uint32_t));
    if (!ranks) return;

    uint32_t n = 0;
    for (uint32_t r = 0; r < p->order_count; r++) {
        if (p->entries[p->order[r]].size >= DEDUP_MIN_SIZE) ranks[n++] = r;
    }
    g_sort = p;
    qsort(ranks, n, sizeof(uint32_t), cmp_size_rank);

    // Only files that share their size with another file can be duplicates
    uint32_t m = 0;
    for (uint32_t i = 0; i < n;) {
        uint32_t j = i;
        uint64_t size = p->entries[p->order[ranks[i]]].size;
        while (j < n && p->entries[p->order[ranks[j]]].size == size) j++;
        if (j - i >= 2) {
            for (uint32_t k = i; k < j; k++) ranks[m++] = ranks[k];
        }
        i = j;
    }
    if (m == 0) {
        free(ranks);
        return;
    }

    printf("\033[32mChecking %u same-size files for duplicates...\033[0m\n", m);
    fflush(stdout);

    hash_job_t job = { .p = p, .ranks = ranks, .count = m, .next = 0 };
    pthread_mutex_init(&job.lock, NULL);
    pthread_t threads[MAX_THREADS];
    int started = 0;
    for (int i = 0; i < p->threads; i++) {
        if (pthread_create(&threads[i], NULL, hash_worker, &job) != 0) break;
        started++;
    }
    if (started == 0) hash_worker(&job);
    for (int i = 0; i < started; i++) pthread_join(threads[i], NULL);
    pthread_mutex_destroy(&job.lock);

    // Same size + same checksum: confirm byte by byte against the earliest copy
    qsort(ranks, m, sizeof(uint32_t), cmp_hash_rank);
    uint8_t *ba = malloc(1 << 20), *bb = malloc(1 << 20);
    if (ba && bb) {
        for (uint32_t i = 0; i < m;) {
            entry_t *canon = &p->entries[p->order[ranks[i]]];
            uint32_t j = i + 1;
            while (j < m) {
                entry_t *e = &p->entries[p->order[ranks[j]]];
                if (!e->pre_ok || !canon->pre_ok || e->size != canon->size || e->pre_crc != canon->pre_crc) break;
                if (files_equal(p, canon, e, ba, bb)) e->dup_of = p->order[ranks[i]];
                j++;
            }
            i = j;
        }
    }
    free(ba);
    free(bb);
    free(ranks);
}

/* ---------- compression pipeline ----------
 * producer thread: reads files in stream order into block-sized slots
 * worker threads:  compress slots in parallel
 * main thread:     writes finished slots to the image strictly in order */

static slot_t* acquire_slot(packer_t *p) {
    pthread_mutex_lock(&p->mutex);
    slot_t *s = &p->slots[p->produced % p->nslots];
    while (s->state != SLOT_FREE) pthread_cond_wait(&p->cond_free, &p->mutex);
    s->state = SLOT_FILLING;
    s->in_len = 0;
    pthread_mutex_unlock(&p->mutex);
    return s;
}

static void submit_slot(packer_t *p, slot_t *s) {
    pthread_mutex_lock(&p->mutex);
    s->state = SLOT_PENDING;
    p->produced++;
    pthread_cond_broadcast(&p->cond_pending);
    pthread_mutex_unlock(&p->mutex);
}

static void* producer_thread(void *arg) {
    packer_t *p = arg;
    slot_t *cur = NULL;
    uint64_t pos = 0;
    char path[MAX_PATH_LEN];

    for (uint32_t r = 0; r < p->order_count; r++) {
        entry_t *e = &p->entries[p->order[r]];

        if (e->dup_of != NO_DUP) {
            // Reuse the identical copy, provided it didn't change since the duplicate scan
            const entry_t *c = &p->entries[e->dup_of];
            if (!c->skipped && c->size == e->size && c->crc == e->pre_crc) {
                e->data_off = c->data_off;
                e->crc = c->crc;
                pthread_mutex_lock(&p->mutex);
                p->current_cloned_size += e->size;
                p->dedup_saved += e->size;
                p->dedup_files++;
                pthread_mutex_unlock(&p->mutex);
                continue;
            }
        }

        source_path(p, e, path, sizeof(path));
        int fd = open_regular(path);
        if (fd < 0) {
            warnf(p, "cannot open %s: %s (skipped)", path, strerror(errno));
            e->skipped = 1;
            continue;
        }
        posix_fadvise(fd, 0, 0, POSIX_FADV_SEQUENTIAL);

        e->data_off = pos;
        uint32_t crc = 0;
        uint64_t got = 0;
        for (;;) {
            if (!cur) cur = acquire_slot(p);
            ssize_t n = read(fd, cur->in + cur->in_len, p->block_size - cur->in_len);
            if (n < 0) {
                if (errno == EINTR) continue;
                warnf(p, "read error on %s: %s (stored first %" PRIu64 " bytes)", path, strerror(errno), got);
                break;
            }
            if (n == 0) break;
            crc = crc32_update(crc, cur->in + cur->in_len, (size_t)n);
            cur->in_len += (uint32_t)n;
            got += (uint64_t)n;
            pos += (uint64_t)n;

            pthread_mutex_lock(&p->mutex);
            p->current_cloned_size += (uint64_t)n;
            pthread_mutex_unlock(&p->mutex);

            if (cur->in_len == p->block_size) {
                submit_slot(p, cur);
                cur = NULL;
            }
        }
        close(fd);
        e->size = got;
        e->crc = crc;
    }

    if (cur) {
        if (cur->in_len > 0) {
            submit_slot(p, cur);
        } else {
            pthread_mutex_lock(&p->mutex);
            cur->state = SLOT_FREE;
            pthread_mutex_unlock(&p->mutex);
        }
    }

    pthread_mutex_lock(&p->mutex);
    p->stream_size = pos;
    p->producer_done = 1;
    pthread_cond_broadcast(&p->cond_pending);
    pthread_cond_broadcast(&p->cond_done);
    pthread_mutex_unlock(&p->mutex);
    return NULL;
}

/* Compresses in[0..n) into out; returns the stored length and type.
 * Every compressed block is decoded again and compared before it is used. */
static uint32_t encode_block(cworker_t *w, packer_t *p, const uint8_t *in, uint32_t n, uint8_t *out, uint8_t *type) {
    *type = BLOCK_STORED;
    if (p->level == 0 || n < 16) return n;

    // Programs and libraries: compress with call addresses made absolute
    uint8_t try_type = BLOCK_CX;
    const uint8_t *src = in;
    if (looks_like_x86(in, n)) {
        memcpy(w->filt, in, n);
        x86_filter(w->filt, n, 1);
        src = w->filt;
        try_type = BLOCK_CX_X86;
    }

    size_t len = cx_compress(w->enc, src, n, out, n - 1);
    if (len == 0) return n;   // incompressible: store raw

    if (decode_typed(try_type, out, (uint32_t)len, w->check, n, w->model) != 0 || memcmp(w->check, in, n) != 0) {
        warnf(p, "compression self-check failed, block stored raw");
        return n;
    }
    *type = try_type;
    return (uint32_t)len;
}

static void* compress_worker(void *arg) {
    cworker_t *w = arg;
    packer_t *p = w->p;
    for (;;) {
        pthread_mutex_lock(&p->mutex);
        while (p->next_compress == p->produced && !p->producer_done) {
            pthread_cond_wait(&p->cond_pending, &p->mutex);
        }
        if (p->next_compress == p->produced) {
            pthread_mutex_unlock(&p->mutex);
            break;
        }
        slot_t *s = &p->slots[p->next_compress % p->nslots];
        p->next_compress++;
        s->state = SLOT_BUSY;
        pthread_mutex_unlock(&p->mutex);

        s->out_len = encode_block(w, p, s->in, s->in_len, s->out, &s->type);

        pthread_mutex_lock(&p->mutex);
        s->state = SLOT_DONE;
        pthread_cond_broadcast(&p->cond_done);
        pthread_mutex_unlock(&p->mutex);
    }
    return NULL;
}

static void out_write(packer_t *p, const void *data, size_t len) {
    if (!p->io_error && write_all(p->out_fd, data, len) != 0) {
        p->io_error = 1;
        p->io_errno = errno;
    }
    p->out_pos += len;
}

static void writer_loop(packer_t *p) {
    for (;;) {
        slot_t *s = NULL;
        pthread_mutex_lock(&p->mutex);
        for (;;) {
            if (p->next_write < p->produced) {
                s = &p->slots[p->next_write % p->nslots];
                if (s->state == SLOT_DONE) break;
                s = NULL;
            } else if (p->producer_done) {
                break;
            }
            pthread_cond_wait(&p->cond_done, &p->mutex);
        }
        pthread_mutex_unlock(&p->mutex);
        if (!s) break;

        if (p->table_count == p->table_cap) {
            uint32_t cap = p->table_cap ? p->table_cap * 2 : 1024;
            block_t *t = (p->table_count < UINT32_MAX / 2) ? realloc(p->table, (size_t)cap * sizeof(block_t)) : NULL;
            if (!t) {
                p->io_error = 1;
                p->io_errno = ENOMEM;
            } else {
                p->table = t;
                p->table_cap = cap;
            }
        }
        if (p->table_count < p->table_cap) {
            block_t *b = &p->table[p->table_count++];
            b->offset = p->out_pos;
            b->stored_len = s->out_len;
            b->type = s->type;
        }
        out_write(p, s->type == BLOCK_STORED ? s->in : s->out, s->out_len);

        pthread_mutex_lock(&p->mutex);
        p->current_output_size = p->out_pos;
        s->state = SLOT_FREE;
        p->next_write++;
        pthread_cond_broadcast(&p->cond_free);
        pthread_mutex_unlock(&p->mutex);
    }
}

/* Appends the extended attributes of path (ACLs, capabilities, labels...)
 * without following symlinks: a count, then name/value records. */
static void put_xattrs(packer_t *p, buf_t *m, const char *path, uint8_t *value) {
    size_t count_pos = m->len;
    uint32_t count = 0;
    buf_u32(m, 0);

    ssize_t list_len = llistxattr(path, NULL, 0);
    if (list_len < 0 && errno != ENOTSUP && errno != ENODATA) {
        warnf(p, "cannot list attributes of %s: %s", path, strerror(errno));
    }
    if (list_len <= 0) return;

    char *list = malloc((size_t)list_len + 1);
    if (!list) {
        m->error = 1;
        return;
    }
    list_len = llistxattr(path, list, (size_t)list_len);
    if (list_len < 0) {
        warnf(p, "cannot list attributes of %s: %s", path, strerror(errno));
        free(list);
        return;
    }
    list[list_len] = '\0';

    for (char *name = list; name < list + list_len; name += strlen(name) + 1) {
        size_t name_len = strlen(name);
        if (name_len == 0 || name_len > XATTR_NAME_MAX_LEN) continue;
        ssize_t value_len = lgetxattr(path, name, value, XATTR_VALUE_MAX_LEN);
        if (value_len < 0) {
            warnf(p, "cannot read attribute %s of %s: %s", name, path, strerror(errno));
            continue;
        }
        buf_u32(m, (uint32_t)name_len);
        buf_put(m, name, name_len);
        buf_u32(m, (uint32_t)value_len);
        buf_put(m, value, (size_t)value_len);
        count++;
    }
    free(list);
    if (!m->error) put_le32(m->p + count_pos, count);
}

static int build_metadata(packer_t *p, buf_t *m, uint32_t *count, uint64_t *original) {
    char path[MAX_PATH_LEN];
    char target[MAX_PATH_LEN];
    *count = 0;
    *original = 0;

    // Position of each entry in the metadata (skipped entries are left out)
    uint32_t *meta_index = malloc((size_t)(p->entry_count ? p->entry_count : 1) * sizeof(uint32_t));
    uint8_t *xattr_value = malloc(XATTR_VALUE_MAX_LEN);
    if (!meta_index || !xattr_value) {
        free(meta_index);
        free(xattr_value);
        return -1;
    }

    for (uint32_t i = 0; i < p->entry_count; i++) {
        entry_t *e = &p->entries[i];
        meta_index[i] = NO_LINK;
        if (e->skipped) continue;

        // A hard link takes its data from the first name of the file
        uint32_t link = NO_LINK;
        if (S_ISREG(e->mode) && e->link_to != NO_LINK) {
            const entry_t *first = &p->entries[e->link_to];
            if (first->skipped || meta_index[e->link_to] == NO_LINK) {
                source_path(p, e, path, sizeof(path));
                warnf(p, "%s is a hard link to a file that could not be read (skipped)", path);
                e->skipped = 1;
                continue;
            }
            link = meta_index[e->link_to];
            e->data_off = first->data_off;
            e->size = first->size;
            e->crc = first->crc;
        }

        source_path(p, e, path, sizeof(path));
        ssize_t tlen = 0;
        if (S_ISLNK(e->mode)) {
            tlen = readlink(path, target, sizeof(target));
            if (tlen < 0 || tlen >= (ssize_t)sizeof(target)) {
                warnf(p, "cannot read symlink %s (skipped)", path);
                e->skipped = 1;
                continue;
            }
        }

        uint32_t path_len = (uint32_t)strlen(e->rel_path);
        buf_u32(m, path_len);
        buf_put(m, e->rel_path, path_len);
        buf_u32(m, e->mode);
        buf_u32(m, e->uid);
        buf_u32(m, e->gid);
        buf_u64(m, (uint64_t)e->mtime);
        buf_u32(m, e->mtime_nsec);
        buf_u64(m, (uint64_t)e->atime);
        buf_u32(m, e->atime_nsec);
        if (S_ISREG(e->mode)) {
            buf_u64(m, e->data_off);
            buf_u64(m, e->size);
            buf_u32(m, e->crc);
            buf_u32(m, link);
            *original += e->size;
        } else if (S_ISLNK(e->mode)) {
            buf_u32(m, (uint32_t)tlen);
            buf_put(m, target, (size_t)tlen);
        } else if (!S_ISDIR(e->mode)) {
            buf_u64(m, e->rdev);
        }
        if (link == NO_LINK) {
            put_xattrs(p, m, path, xattr_value);
        } else {
            buf_u32(m, 0);   // a hard link shares the attributes of its first name
        }
        meta_index[i] = *count;
        (*count)++;
    }
    free(meta_index);
    free(xattr_value);
    return m->error ? -1 : 0;
}

static int write_image(packer_t *p) {
    uint8_t hdr[HEADER_SIZE] = {0};
    out_write(p, hdr, HEADER_SIZE);   // placeholder, rewritten at the end

    // Pipeline buffers
    p->nslots = (uint32_t)p->threads * 2 + 2;
    p->slots = calloc(p->nslots, sizeof(slot_t));
    cworker_t *workers = calloc((size_t)p->threads, sizeof(cworker_t));
    if (!p->slots || !workers) goto oom;
    for (uint32_t i = 0; i < p->nslots; i++) {
        p->slots[i].in = malloc(p->block_size);
        p->slots[i].out = malloc(p->block_size);
        if (!p->slots[i].in || !p->slots[i].out) goto oom;
    }
    for (int i = 0; i < p->threads; i++) {
        cworker_t *w = &workers[i];
        w->p = p;
        w->enc = cx_enc_create(p->level, p->block_size);
        w->model = malloc(sizeof(model_t));
        w->check = malloc(p->block_size);
        w->filt = malloc(p->block_size);
        if (!w->enc || !w->model || !w->check || !w->filt) goto oom;
    }
    pthread_cond_init(&p->cond_free, NULL);
    pthread_cond_init(&p->cond_pending, NULL);
    pthread_cond_init(&p->cond_done, NULL);

    printf("\033[32mCompressing %u files with %d threads (level %d, %u KiB blocks)...\033[0m\n",
           p->order_count, p->threads, p->level, p->block_size >> 10);
    fflush(stdout);

    if (p->show_progress) {
        // hide the cursor and turn off line wrap so the progress line can never spill onto a new line
        printf("\033[?25l\033[?7l");
        fflush(stdout);
        g_term_dirty = 1;
        p->progress_running = 1;
        if (pthread_create(&p->progress_thread, NULL, progress_thread, p) != 0) p->progress_running = 0;
    }

    pthread_t producer;
    pthread_t threads[MAX_THREADS];
    int started = 0;
    if (pthread_create(&producer, NULL, producer_thread, p) != 0) goto oom;
    for (int i = 0; i < p->threads; i++) {
        if (pthread_create(&threads[i], NULL, compress_worker, &workers[i]) != 0) break;
        started++;
    }
    if (started == 0) {
        restore_terminal();
        fprintf(stderr, "\033[31mError: cannot start worker threads\033[0m\n");
        exit(1);
    }

    writer_loop(p);

    pthread_join(producer, NULL);
    for (int i = 0; i < started; i++) pthread_join(threads[i], NULL);

    pthread_mutex_lock(&p->mutex);
    int was_running = p->progress_running;
    p->progress_running = 0;
    pthread_mutex_unlock(&p->mutex);
    if (was_running) {
        pthread_join(p->progress_thread, NULL);
        pthread_mutex_lock(&p->mutex);
        draw_progress(p, 100.0f);
        pthread_mutex_unlock(&p->mutex);
    }
    if (p->show_progress) {
        printf("\n");
        fflush(stdout);
        restore_terminal();
    }
    if (p->deferred.len > 0) {
        fprintf(stderr, "\033[33m");
        const char *s = (const char*)p->deferred.p;
        size_t left = p->deferred.len;
        while (left > 0) {
            const char *nl = memchr(s, '\n', left);
            size_t len = nl ? (size_t)(nl - s) : left;
            fprintf(stderr, "Warning: %.*s\n", (int)len, s);
            if (!nl) break;
            left -= len + 1;
            s = nl + 1;
        }
        fprintf(stderr, "\033[0m");
    }

    // Block table
    header_t h;
    memset(&h, 0, sizeof(h));
    h.version = FORMAT_VERSION;
    h.level = (uint8_t)p->level;
    h.block_size = p->block_size;
    h.block_count = p->table_count;
    h.data_size = p->stream_size;
    h.block_table_off = p->out_pos;
    uint32_t crc = 0;
    for (uint32_t i = 0; i < p->table_count; i++) {
        uint8_t e[BLOCK_ENTRY_SIZE] = {0};
        put_le64(e, p->table[i].offset);
        put_le32(e + 8, p->table[i].stored_len);
        e[12] = p->table[i].type;
        crc = crc32_update(crc, e, sizeof(e));
        out_write(p, e, sizeof(e));
    }
    h.block_table_crc = crc;

    // Metadata, compressed in block-sized chunks with the same codec
    buf_t meta = {0};
    uint32_t node_count;
    if (build_metadata(p, &meta, &node_count, &h.original_size) != 0) goto oom;
    h.node_count = node_count;
    h.meta_raw_len = meta.len;
    h.meta_crc = crc32_update(0, meta.p, meta.len);
    h.meta_off = p->out_pos;
    uint8_t *packed = malloc(p->block_size);
    if (!packed) goto oom;
    for (size_t off = 0; off < meta.len;) {
        uint32_t n = meta.len - off > p->block_size ? p->block_size : (uint32_t)(meta.len - off);
        uint8_t type;
        uint32_t len = encode_block(&workers[0], p, meta.p + off, n, packed, &type);
        uint8_t ch[CHUNK_HEADER_SIZE];
        put_le32(ch, n);
        put_le32(ch + 4, len);
        ch[8] = type;
        out_write(p, ch, sizeof(ch));
        out_write(p, type == BLOCK_STORED ? meta.p + off : packed, len);
        off += n;
    }
    h.meta_stored_len = p->out_pos - h.meta_off;
    free(packed);
    free(meta.p);

    // Footer and final header
    uint8_t footer[FOOTER_SIZE];
    memcpy(footer, FOOTER_MAGIC, 4);
    put_le32(footer + 4, node_count);
    out_write(p, footer, sizeof(footer));
    h.image_size = p->out_pos;
    header_encode(&h, hdr);
    if (!p->io_error && pwrite(p->out_fd, hdr, HEADER_SIZE, 0) != HEADER_SIZE) {
        p->io_error = 1;
        p->io_errno = errno;
    }
    if (!p->io_error && fsync(p->out_fd) != 0 && errno == EIO) {
        p->io_error = 1;
        p->io_errno = errno;
    }
    if (p->io_error) {
        fprintf(stderr, "\033[31mError writing image: %s\033[0m\n", strerror(p->io_errno));
        return -1;
    }

    // Summary
    time_t secs = time(NULL) - p->start_time;
    char orig_str[32], img_str[32], dup_str[32];
    format_size(h.original_size, orig_str, sizeof(orig_str));
    format_size(h.image_size, img_str, sizeof(img_str));
    printf("\033[32mCreated: %s\033[0m\n", p->output_name);
    printf("\033[32mEntries: %u   Original: %s   Image: %s", node_count, orig_str, img_str);
    if (h.original_size > 0) printf("   Ratio: %.1f%%", 100.0 * h.image_size / h.original_size);
    printf("\033[0m\n");
    if (p->dedup_files > 0) {
        format_size(p->dedup_saved, dup_str, sizeof(dup_str));
        printf("\033[32mDuplicates: %u files (%s) stored once\033[0m\n", p->dedup_files, dup_str);
    }
    if (secs > 0) {
        char speed[32];
        format_size(h.original_size / (uint64_t)secs, speed, sizeof(speed));
        printf("\033[32mTime: %lds (%s/s)\033[0m\n", (long)secs, speed);
    }
    return 0;

oom:
    restore_terminal();
    fprintf(stderr, "\033[31mError: out of memory\033[0m\n");
    return -1;
}

static int parse_size(const char *s, uint64_t *out) {
    char *end;
    unsigned long long v = strtoull(s, &end, 10);
    if (end == s) return -1;
    if (*end == 'k' || *end == 'K') { v <<= 10; end++; }
    else if (*end == 'm' || *end == 'M') { v <<= 20; end++; }
    else if (*end == 'g' || *end == 'G') { v <<= 30; end++; }
    if (*end == 'i' || *end == 'I') end++;
    if (*end == 'b' || *end == 'B') end++;
    if (*end != '\0') return -1;
    *out = v;
    return 0;
}

static int cmd_create(int argc, char **argv) {
    packer_t *p = calloc(1, sizeof(packer_t));
    if (!p) return 1;
    p->level = DEFAULT_LEVEL;
    p->block_size = DEFAULT_BLOCK_SIZE;
    p->threads = (int)sysconf(_SC_NPROCESSORS_ONLN);
    p->dedup = 1;
    p->default_excludes_on = 1;
    p->start_time = time(NULL);
    pthread_mutex_init(&p->mutex, NULL);

    const char *source = NULL, *output = NULL;
    int quiet = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-l") == 0 && i + 1 < argc) {
            p->level = atoi(argv[++i]);
            if (p->level < 0) p->level = 0;
            if (p->level > MAX_LEVEL) p->level = MAX_LEVEL;
        } else if (strcmp(argv[i], "-b") == 0 && i + 1 < argc) {
            uint64_t bs;
            if (parse_size(argv[++i], &bs) != 0 || bs < MIN_BLOCK_SIZE || bs > MAX_BLOCK_SIZE) {
                fprintf(stderr, "\033[31mError: block size must be between 64K and 64M\033[0m\n");
                return 1;
            }
            p->block_size = (uint32_t)bs;
        } else if (strcmp(argv[i], "-T") == 0 && i + 1 < argc) {
            p->threads = atoi(argv[++i]);
        } else if (strcmp(argv[i], "-q") == 0) {
            quiet = 1;
        } else if (strcmp(argv[i], "--no-dedup") == 0) {
            p->dedup = 0;
        } else if (strcmp(argv[i], "--no-default-excludes") == 0) {
            p->default_excludes_on = 0;
        } else if (strncmp(argv[i], "--exclude=", 10) == 0) {
            continue;   // handled once the source is known
        } else if (argv[i][0] == '-' && argv[i][1] != '\0') {
            fprintf(stderr, "\033[31mError: unknown option %s\033[0m\n", argv[i]);
            return 1;
        } else if (!source) {
            source = argv[i];
        } else if (!output) {
            output = argv[i];
        }
    }
    if (p->threads < 1) p->threads = 1;
    if (p->threads > MAX_THREADS) p->threads = MAX_THREADS;

    if (!source || !output) {
        fprintf(stderr, "\033[31mError: usage: mkfs.claudex create [options] <source-dir> <image>\033[0m\n");
        return 1;
    }

    // An existing folder gets root.claudex inside it; otherwise add .claudex if missing
    char final_output[MAX_PATH_LEN];
    char out_dir[MAX_PATH_LEN];
    snprintf(out_dir, sizeof(out_dir), "%s", output);
    strip_trailing_slashes(out_dir);
    size_t out_len = strlen(out_dir);
    struct stat out_dir_st;
    if (stat(out_dir, &out_dir_st) == 0 && S_ISDIR(out_dir_st.st_mode)) {
        join_path(final_output, sizeof(final_output), out_dir, "root.claudex", NULL);
    } else if (out_len < 8 || strcmp(out_dir + out_len - 8, ".claudex") != 0) {
        snprintf(final_output, sizeof(final_output), "%s.claudex", out_dir);
    } else {
        snprintf(final_output, sizeof(final_output), "%s", out_dir);
    }
    if (mkdir_parent(final_output, 0755) != 0) {
        fprintf(stderr, "\033[31mError: cannot create the folders for '%s': %s\033[0m\n", final_output, strerror(errno));
        return 1;
    }
    snprintf(p->output_name, sizeof(p->output_name), "%s", base_name(final_output));
    p->show_progress = !quiet && isatty(STDOUT_FILENO);

    char *resolved = realpath(source, NULL);
    snprintf(p->source_root, sizeof(p->source_root), "%s", resolved ? resolved : source);
    free(resolved);
    strip_trailing_slashes(p->source_root);

    struct stat root_st;
    if (stat(p->source_root, &root_st) != 0 || !S_ISDIR(root_st.st_mode)) {
        fprintf(stderr, "\033[31mError: '%s' is not a directory\033[0m\n", source);
        return 1;
    }

    if (p->default_excludes_on) {
        printf("\033[32mDefault excludes:");
        for (int i = 0; default_exclude_names[i]; i++) printf(" %s", default_exclude_names[i]);
        for (int i = 0; default_excludes[i]; i++) {
            // Packing /tmp/foo itself is fine: only skip defaults that lie inside the source
            if (path_is_under(p->source_root, default_excludes[i])) continue;
            add_exclude_path(&p->excludes, default_excludes[i]);
            printf(" %s", default_excludes[i]);
        }
        printf("\033[0m\n");
    }
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "--exclude=", 10) == 0) {
            add_exclude_path(&p->excludes, argv[i] + 10);
            printf("\033[32mExcluding path: %s\033[0m\n", argv[i] + 10);
        }
    }

    p->out_fd = open(final_output, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
    if (p->out_fd < 0) {
        fprintf(stderr, "\033[31mError: cannot create '%s': %s\033[0m\n", final_output, strerror(errno));
        return 1;
    }
    struct stat out_st;
    if (fstat(p->out_fd, &out_st) == 0) {
        p->output_dev = out_st.st_dev;
        p->output_ino = out_st.st_ino;
    }

    // Ctrl-C: put the terminal back and don't leave a half-written image behind
    snprintf(g_partial_output, sizeof(g_partial_output), "%s", final_output);
    signal(SIGINT, on_signal);
    signal(SIGTERM, on_signal);
    signal(SIGHUP, on_signal);

    printf("\033[32mScanning %s...\033[0m\n", p->source_root);
    fflush(stdout);
    int rc = 0;
    if (add_entry(p, "", &root_st) != 0 || traverse_directory(p, p->source_root, "") != 0) {
        fprintf(stderr, "\033[31mError: out of memory while scanning\033[0m\n");
        rc = 1;
    }

    if (rc == 0) {
        p->order = malloc((size_t)(p->entry_count ? p->entry_count : 1) * sizeof(uint32_t));
        if (!p->order) {
            rc = 1;
        } else {
            find_hard_links(p);
            for (uint32_t i = 0; i < p->entry_count; i++) {
                if (S_ISREG(p->entries[i].mode) && p->entries[i].link_to == NO_LINK) {
                    p->order[p->order_count++] = i;
                }
            }
            g_sort = p;
            qsort(p->order, p->order_count, sizeof(uint32_t), cmp_stream_order);
            if (p->dedup) find_duplicates(p);
            if (write_image(p) != 0) rc = 1;
        }
    }

    if (close(p->out_fd) != 0 && rc == 0) {
        fprintf(stderr, "\033[31mError closing image: %s\033[0m\n", strerror(errno));
        rc = 1;
    }
    if (rc != 0) {
        unlink(final_output);
        return rc;
    }
    g_partial_output[0] = '\0';
    if (p->warnings > 0) {
        printf("\033[33mDone with %u warning(s) - some entries were skipped or truncated.\033[0m\n", p->warnings);
        return 2;
    }
    printf("\033[32mDone.\033[0m\n");
    return 0;
}

/* =====================================================================
 *  extract / test / list / info
 * ===================================================================== */

typedef struct {
    char *path;
    char *target;
    uint32_t mode, uid, gid;
    int64_t mtime, atime;
    uint32_t mtime_nsec, atime_nsec;
    uint64_t data_off, size, rdev;
    uint32_t crc;
    uint32_t link;          // hard link to this earlier entry, or NO_LINK
    uint32_t xattr_count;
    const uint8_t *xattrs;  // points into the image's metadata
} xentry_t;

static uint32_t error_count;
static uint32_t restore_warnings;

static void restore_warn(const char *path, const char *what) {
    restore_warnings++;
    fprintf(stderr, "\033[33mWarning: %s: cannot restore %s: %s\033[0m\n", path, what, strerror(errno));
}

/* Puts back owner, extended attributes (ACLs, capabilities...), permissions
 * and timestamps. Order matters: changing the owner clears capabilities, and
 * attributes must be set while the file is still writable. Uses fd when
 * given, otherwise the path itself (never following a symlink). */
static void restore_meta(const xentry_t *x, const char *full, int fd, int is_root) {
    int is_link = S_ISLNK(x->mode);

    if (is_root && (fd >= 0 ? fchown(fd, x->uid, x->gid) : lchown(full, x->uid, x->gid)) != 0) {
        restore_warn(x->path, "owner");
    }

    const uint8_t *rec = x->xattrs;
    char name[XATTR_NAME_MAX_LEN + 1];
    for (uint32_t i = 0; i < x->xattr_count; i++) {
        const uint8_t *value;
        uint32_t value_len;
        rec = xattr_next(rec, name, &value, &value_len);
        int r = fd >= 0 ? fsetxattr(fd, name, value, value_len, 0)
                        : lsetxattr(full, name, value, value_len, 0);
        if (r != 0) {
            char what[XATTR_NAME_MAX_LEN + 16];
            snprintf(what, sizeof(what), "attribute %s", name);
            restore_warn(x->path, what);
        }
    }

    if (!is_link && (fd >= 0 ? fchmod(fd, x->mode & 07777) : chmod(full, x->mode & 07777)) != 0) {
        restore_warn(x->path, "permissions");
    }

    struct timespec ts[2];
    ts[0].tv_sec = x->atime;
    ts[0].tv_nsec = x->atime_nsec;
    ts[1].tv_sec = x->mtime;
    ts[1].tv_nsec = x->mtime_nsec;
    if ((fd >= 0 ? futimens(fd, ts) : utimensat(AT_FDCWD, full, ts, AT_SYMLINK_NOFOLLOW)) != 0) {
        restore_warn(x->path, "timestamps");
    }
}

static void report(const char *fmt, ...) __attribute__((format(printf, 1, 2)));

static void report(const char *fmt, ...) {
    va_list ap;
    error_count++;
    fprintf(stderr, "\033[31mError: ");
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\033[0m\n");
}

/* Create the directories along dest/rel, refusing to pass through anything
 * that is not a real directory (e.g. a symlink planted by an earlier entry).
 * With include_last == 0 only the parents of the final component are made. */
static int make_dirs(const char *dest, const char *rel, int include_last) {
    char path[MAX_PATH_LEN * 2];
    int n = snprintf(path, sizeof(path), "%s/%s", dest, rel);
    if (n < 0 || (size_t)n >= sizeof(path)) {
        errno = ENAMETOOLONG;
        return -1;
    }
    char *s = path + strlen(dest) + 1;
    for (;;) {
        char *slash = strchr(s, '/');
        if (!slash && !include_last) break;
        if (slash) *slash = '\0';
        struct stat st;
        if (lstat(path, &st) == 0) {
            if (!S_ISDIR(st.st_mode)) {
                errno = ENOTDIR;
                return -1;
            }
        } else if (errno == ENOENT) {
            if (mkdir(path, 0700) != 0 && errno != EEXIST) return -1;
        } else {
            return -1;
        }
        if (!slash) break;
        *slash = '/';
        s = slash + 1;
    }
    return 0;
}

// Remove whatever non-directory currently sits at path
static int clear_path(const char *path) {
    struct stat st;
    if (lstat(path, &st) != 0) return errno == ENOENT ? 0 : -1;
    if (S_ISDIR(st.st_mode)) {
        errno = EISDIR;
        return -1;
    }
    return unlink(path);
}

static xentry_t *g_xentries;

static int cmp_data_off(const void *a, const void *b) {
    const xentry_t *x = &g_xentries[*(const uint32_t*)a];
    const xentry_t *y = &g_xentries[*(const uint32_t*)b];
    if (x->data_off != y->data_off) return x->data_off < y->data_off ? -1 : 1;
    return *(const uint32_t*)a < *(const uint32_t*)b ? -1 : 1;
}

static void mode_string(uint32_t mode, char out[11]) {
    char t = '-';
    if (S_ISDIR(mode)) t = 'd';
    else if (S_ISLNK(mode)) t = 'l';
    else if (S_ISCHR(mode)) t = 'c';
    else if (S_ISBLK(mode)) t = 'b';
    else if (S_ISFIFO(mode)) t = 'p';
    else if (S_ISSOCK(mode)) t = 's';
    out[0] = t;
    const char *rwx = "rwxrwxrwx";
    for (int i = 0; i < 9; i++) out[i + 1] = (mode & (1u << (8 - i))) ? rwx[i] : '-';
    out[10] = '\0';
}

static int open_or_die(image_t *img, const char *path) {
    char err[512];
    if (image_open(img, path, err, sizeof(err)) != 0) {
        fprintf(stderr, "\033[31mError: %s\033[0m\n", err);
        return -1;
    }
    return 0;
}

static int cmd_list(const char *image) {
    image_t img;
    if (open_or_die(&img, image) != 0) return 1;
    // Remember each entry's path so hard links can name their target
    const char **paths = calloc(img.h.node_count ? img.h.node_count : 1, sizeof(char*));
    uint32_t *lens = calloc(img.h.node_count ? img.h.node_count : 1, sizeof(uint32_t));
    if (!paths || !lens) {
        fprintf(stderr, "\033[31mError: out of memory\033[0m\n");
        return 1;
    }
    size_t pos = 0;
    uint32_t i = 0;
    meta_entry_t e;
    while (meta_next(&img, &pos, &e) == 1) {
        paths[i] = e.path;
        lens[i] = e.path_len;
        char ms[11];
        mode_string(e.mode, ms);
        printf("%s %8u %8u %12" PRIu64 "  %.*s", ms, e.uid, e.gid, e.size,
               e.path_len ? (int)e.path_len : 1, e.path_len ? e.path : ".");
        if (S_ISLNK(e.mode)) printf(" -> %.*s", (int)e.target_len, e.target);
        if (e.link != NO_LINK) printf(" (hard link to %.*s)", (int)lens[e.link], paths[e.link]);
        printf("\n");
        i++;
    }
    free(paths);
    free(lens);
    image_close(&img);
    return 0;
}

static int cmd_info(const char *image) {
    image_t img;
    if (open_or_die(&img, image) != 0) return 1;
    const header_t *h = &img.h;
    uint32_t cx_blocks = 0;
    for (uint32_t i = 0; i < h->block_count; i++) cx_blocks += img.blocks[i].type != BLOCK_STORED;
    char a[32], b[32], c[32], d[32];
    format_size(h->original_size, a, sizeof(a));
    format_size(h->data_size, b, sizeof(b));
    format_size(h->image_size, c, sizeof(c));
    format_size(h->meta_stored_len, d, sizeof(d));
    printf("Format version:   %u\n", h->version);
    printf("Level:            %u\n", h->level);
    printf("Entries:          %u\n", h->node_count);
    printf("Files total:      %s\n", a);
    printf("Stored once:      %s (after removing duplicates)\n", b);
    printf("Image size:       %s", c);
    if (h->original_size) printf(" (%.1f%% of original)", 100.0 * h->image_size / h->original_size);
    printf("\n");
    printf("Blocks:           %u x %u KiB (%u compressed, %u stored raw)\n",
           h->block_count, h->block_size >> 10, cx_blocks, h->block_count - cx_blocks);
    printf("Metadata:         %s\n", d);
    image_close(&img);
    return 0;
}

// dest == NULL: verify only
static int cmd_extract(const char *image, const char *dest, int verbose) {
    image_t img;
    if (open_or_die(&img, image) != 0) return 1;
    const header_t *h = &img.h;

    xentry_t *xs = calloc(h->node_count ? h->node_count : 1, sizeof(xentry_t));
    uint32_t *files = malloc((size_t)(h->node_count ? h->node_count : 1) * sizeof(uint32_t));
    uint8_t *buf = malloc(h->block_size);
    block_cache_t cache;
    if (!xs || !files || !buf || cache_init(&cache, &img) != 0) {
        fprintf(stderr, "\033[31mError: out of memory\033[0m\n");
        return 1;
    }

    uint32_t n = 0, nfiles = 0;
    size_t pos = 0;
    meta_entry_t e;
    while (meta_next(&img, &pos, &e) == 1) {
        xentry_t *x = &xs[n];
        x->path = strndup(e.path, e.path_len);
        x->target = S_ISLNK(e.mode) ? strndup(e.target, e.target_len) : NULL;
        if (!x->path || (S_ISLNK(e.mode) && !x->target)) {
            fprintf(stderr, "\033[31mError: out of memory\033[0m\n");
            return 1;
        }
        x->mode = e.mode;
        x->uid = e.uid;
        x->gid = e.gid;
        x->mtime = e.mtime;
        x->mtime_nsec = e.mtime_nsec;
        x->atime = e.atime;
        x->atime_nsec = e.atime_nsec;
        x->xattr_count = e.xattr_count;
        x->xattrs = e.xattrs;
        x->data_off = e.data_off;
        x->size = e.size;
        x->crc = e.crc;
        x->rdev = e.rdev;
        x->link = e.link;
        if (!safe_rel_path(x->path)) {
            report("unsafe path skipped: %s", x->path);
            x->mode = 0;
        } else if (S_ISREG(x->mode) && x->link == NO_LINK) {
            files[nfiles++] = n;    // hard links are made after their target exists
        }
        n++;
    }

    char *dest_abs = NULL;
    int is_root = 0;
    if (dest) {
        if (mkdir_p(dest, 0755) != 0) {
            fprintf(stderr, "\033[31mError: cannot create '%s': %s\033[0m\n", dest, strerror(errno));
            return 1;
        }
        dest_abs = realpath(dest, NULL);
        if (!dest_abs) {
            fprintf(stderr, "\033[31mError: cannot resolve '%s': %s\033[0m\n", dest, strerror(errno));
            return 1;
        }
        dest = dest_abs;
        is_root = (geteuid() == 0);
        umask(0);
        if (!is_root) {
            fprintf(stderr, "\033[33mNote: not running as root - file owners, file capabilities and some attributes\n"
                            "cannot be restored. Use sudo for an exact copy.\033[0m\n");
        }
    }

    char full[MAX_PATH_LEN * 2];

    // 1. Directories (parents come first in the metadata)
    if (dest) {
        for (uint32_t i = 0; i < n; i++) {
            xentry_t *x = &xs[i];
            if (!S_ISDIR(x->mode) || x->path[0] == '\0') continue;
            if (verbose) printf("%s/\n", x->path);
            if (make_dirs(dest, x->path, 1) != 0) report("%s: cannot create directory: %s", x->path, strerror(errno));
        }
    }

    // 2. Files, in data stream order so every block is decoded only once
    g_xentries = xs;
    qsort(files, nfiles, sizeof(uint32_t), cmp_data_off);
    uint64_t total = 0;
    for (uint32_t k = 0; k < nfiles; k++) {
        xentry_t *x = &xs[files[k]];
        int fd = -1;
        if (dest) {
            if (verbose) printf("%s\n", x->path);
            snprintf(full, sizeof(full), "%s/%s", dest, x->path);
            if (make_dirs(dest, x->path, 0) != 0 || clear_path(full) != 0 ||
                (fd = open(full, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600)) < 0) {
                report("%s: cannot create file: %s", x->path, strerror(errno));
                continue;
            }
        }

        uint32_t crc = 0;
        uint64_t done = 0;
        int bad = 0;
        while (done < x->size) {
            size_t chunk = x->size - done > h->block_size ? h->block_size : (size_t)(x->size - done);
            if (read_stream(&cache, x->data_off + done, buf, chunk) != 0) {
                report("%s: corrupt data at offset %" PRIu64, x->path, done);
                bad = 1;
                break;
            }
            crc = crc32_update(crc, buf, chunk);
            if (fd >= 0 && write_all(fd, buf, chunk) != 0) {
                report("%s: write failed: %s", x->path, strerror(errno));
                bad = 1;
                break;
            }
            done += chunk;
        }
        if (!bad && crc != x->crc) report("%s: checksum mismatch", x->path);
        total += done;

        if (fd >= 0) {
            restore_meta(x, full, fd, is_root);
            if (close(fd) != 0) report("%s: write failed: %s", x->path, strerror(errno));
        }
    }

    // 3. Hard links to the files written above
    if (dest) {
        char target_full[MAX_PATH_LEN * 2];
        for (uint32_t i = 0; i < n; i++) {
            xentry_t *x = &xs[i];
            if (x->mode == 0 || !S_ISREG(x->mode) || x->link == NO_LINK) continue;
            if (verbose) printf("%s\n", x->path);
            const xentry_t *t = &xs[x->link];
            if (t->mode == 0) {
                report("%s: hard link target was skipped", x->path);
                continue;
            }
            snprintf(full, sizeof(full), "%s/%s", dest, x->path);
            snprintf(target_full, sizeof(target_full), "%s/%s", dest, t->path);
            if (make_dirs(dest, x->path, 0) != 0 || clear_path(full) != 0 || link(target_full, full) != 0) {
                report("%s: cannot create hard link to %s: %s", x->path, t->path, strerror(errno));
            }
        }
    }

    // 4. Symlinks and special files
    if (dest) {
        for (uint32_t i = 0; i < n; i++) {
            xentry_t *x = &xs[i];
            if (x->mode == 0 || S_ISDIR(x->mode) || S_ISREG(x->mode) || S_ISSOCK(x->mode)) continue;
            if (verbose) printf("%s\n", x->path);
            snprintf(full, sizeof(full), "%s/%s", dest, x->path);
            if (make_dirs(dest, x->path, 0) != 0 || clear_path(full) != 0) {
                report("%s: cannot create: %s", x->path, strerror(errno));
                continue;
            }
            int r;
            if (S_ISLNK(x->mode)) r = symlink(x->target, full);
            else if (S_ISFIFO(x->mode)) r = mkfifo(full, x->mode & 07777);
            else r = mknod(full, (x->mode & S_IFMT) | (x->mode & 07777), (dev_t)x->rdev);
            if (r != 0) {
                if (S_ISLNK(x->mode)) {
                    report("%s: cannot create symlink: %s", x->path, strerror(errno));
                } else {
                    // Device nodes need root; not a data error
                    fprintf(stderr, "\033[33mWarning: %s: cannot create special file: %s\033[0m\n", x->path, strerror(errno));
                }
                continue;
            }
            restore_meta(x, full, -1, is_root);
        }

        // 5. Directory owners, attributes, permissions and times last, deepest first
        for (uint32_t i = n; i-- > 0;) {
            xentry_t *x = &xs[i];
            if (!S_ISDIR(x->mode) || x->path[0] == '\0') continue;
            snprintf(full, sizeof(full), "%s/%s", dest, x->path);
            restore_meta(x, full, -1, is_root);
        }
    }

    for (uint32_t i = 0; i < n; i++) {
        free(xs[i].path);
        free(xs[i].target);
    }
    free(xs);
    free(files);
    free(buf);
    free(dest_abs);
    cache_free(&cache);
    image_close(&img);

    char tot[32];
    format_size(total, tot, sizeof(tot));
    if (error_count > 0) {
        fprintf(stderr, "\033[31m%u error(s) in %u entries.\033[0m\n", error_count, n);
        return 1;
    }
    if (restore_warnings > 0) {
        printf("\033[33mExtracted %u entries (%s), but %u owner/permission/attribute/time setting(s) could not be\n"
               "restored - see the warnings above.\033[0m\n", n, tot, restore_warnings);
        return 2;
    }
    printf("\033[32mOK: %u entries, %s of file data verified%s.\033[0m\n", n, tot, dest ? " and extracted" : "");
    return 0;
}

/* =====================================================================
 *  mount (FUSE, read-only)
 * ===================================================================== */

typedef struct mnode {
    char *path;              // relative, "" for the root
    const char *name;        // last component (points into path)
    uint32_t mode, uid, gid;
    int64_t mtime, atime;
    uint32_t mtime_nsec, atime_nsec;
    uint64_t size, data_off, rdev, ino;
    char *target;
    uint32_t xattr_count;
    const uint8_t *xattrs;   // points into the image's metadata
    struct mnode *owner;     // hard links: the first name of the file (itself otherwise)
    uint32_t links;          // on the owner: number of names for the file
    struct mnode **children;
    uint32_t nchildren, children_cap, nsubdirs;
} mnode_t;

static image_t g_img;
static mnode_t *g_nodes;
static uint32_t g_node_count;
static mnode_t **g_table;
static uint32_t g_mask;
static pthread_key_t g_cache_key;

// Decoded blocks shared by all FUSE threads (least recently used is replaced)
#define LRU_BYTES (64u << 20)

typedef struct {
    int64_t index;
    uint64_t stamp;
    uint8_t *data;
} lru_entry_t;

static lru_entry_t *g_lru;
static uint32_t g_lru_count;
static uint64_t g_lru_clock;
static pthread_mutex_t g_lru_lock = PTHREAD_MUTEX_INITIALIZER;

static uint32_t hash_path(const char *p, size_t len) {
    uint32_t h = 2166136261u;
    for (size_t i = 0; i < len; i++) {
        h ^= (uint8_t)p[i];
        h *= 16777619u;
    }
    return h;
}

static mnode_t* mlookup_n(const char *path, size_t len) {
    for (uint32_t i = hash_path(path, len) & g_mask;; i = (i + 1) & g_mask) {
        mnode_t *n = g_table[i];
        if (!n) return NULL;
        if (strlen(n->path) == len && memcmp(n->path, path, len) == 0) return n;
    }
}

static mnode_t* mlookup(const char *path) {
    while (*path == '/') path++;
    return mlookup_n(path, strlen(path));
}

static int build_mount_index(void) {
    g_nodes = calloc(g_img.h.node_count ? g_img.h.node_count : 1, sizeof(mnode_t));
    uint32_t table_size = 16;
    while (table_size < (uint64_t)g_img.h.node_count * 2) table_size *= 2;
    g_table = calloc(table_size, sizeof(mnode_t*));
    g_mask = table_size - 1;
    // metadata position -> node, to resolve hard links
    mnode_t **by_meta = calloc(g_img.h.node_count ? g_img.h.node_count : 1, sizeof(mnode_t*));
    if (!g_nodes || !g_table || !by_meta) return -1;

    size_t pos = 0;
    uint32_t meta_pos = 0;
    meta_entry_t e;
    while (meta_next(&g_img, &pos, &e) == 1) {
        uint32_t this_meta = meta_pos++;
        mnode_t *n = &g_nodes[g_node_count];
        n->path = strndup(e.path, e.path_len);
        if (!n->path) return -1;
        if (!safe_rel_path(n->path) || mlookup_n(n->path, e.path_len)) {
            fprintf(stderr, "claudex: skipping bad or duplicate path '%s'\n", n->path);
            free(n->path);
            continue;
        }
        const char *slash = strrchr(n->path, '/');
        n->name = slash ? slash + 1 : n->path;
        n->mode = e.mode;
        n->uid = e.uid;
        n->gid = e.gid;
        n->mtime = e.mtime;
        n->mtime_nsec = e.mtime_nsec;
        n->atime = e.atime;
        n->atime_nsec = e.atime_nsec;
        n->xattr_count = e.xattr_count;
        n->xattrs = e.xattrs;
        n->size = S_ISLNK(e.mode) ? e.target_len : e.size;
        n->data_off = e.data_off;
        n->rdev = e.rdev;
        n->ino = g_node_count + 1;
        n->owner = n;
        n->links = 1;
        if (e.link != NO_LINK && by_meta[e.link]) {
            // Another name for an earlier file: same inode, one more link
            n->owner = by_meta[e.link];
            n->owner->links++;
        }
        if (S_ISLNK(e.mode)) {
            n->target = strndup(e.target, e.target_len);
            if (!n->target) return -1;
        }

        if (e.path_len > 0) {
            // Parents are always stored before their contents
            mnode_t *parent = mlookup_n(n->path, slash ? (size_t)(slash - n->path) : 0);
            if (!parent || !S_ISDIR(parent->mode)) {
                fprintf(stderr, "claudex: '%s' has no parent directory, skipped\n", n->path);
                if (n->owner != n) n->owner->links--;
                free(n->path);
                free(n->target);
                continue;
            }
            if (parent->nchildren == parent->children_cap) {
                uint32_t cap = parent->children_cap ? parent->children_cap * 2 : 8;
                mnode_t **c = realloc(parent->children, cap * sizeof(mnode_t*));
                if (!c) return -1;
                parent->children = c;
                parent->children_cap = cap;
            }
            parent->children[parent->nchildren++] = n;
            if (S_ISDIR(n->mode)) parent->nsubdirs++;
        }

        for (uint32_t i = hash_path(n->path, e.path_len) & g_mask;; i = (i + 1) & g_mask) {
            if (!g_table[i]) {
                g_table[i] = n;
                break;
            }
        }
        by_meta[this_meta] = n;
        g_node_count++;
    }
    free(by_meta);

    mnode_t *root = mlookup("");
    if (!root || !S_ISDIR(root->mode)) {
        fprintf(stderr, "claudex: image has no root directory\n");
        return -1;
    }
    return 0;
}

static void free_thread_cache(void *arg) {
    block_cache_t *c = arg;
    cache_free(c);
    free(c);
}

static block_cache_t* thread_cache(void) {
    block_cache_t *c = pthread_getspecific(g_cache_key);
    if (c) return c;
    c = calloc(1, sizeof(block_cache_t));
    if (!c) return NULL;
    if (cache_init(c, &g_img) != 0) {
        cache_free(c);
        free(c);
        return NULL;
    }
    pthread_setspecific(g_cache_key, c);
    return c;
}

static void fill_stat(const mnode_t *n, struct stat *st) {
    memset(st, 0, sizeof(*st));
    st->st_ino = n->owner->ino;
    st->st_mode = n->mode;
    st->st_uid = n->uid;
    st->st_gid = n->gid;
    st->st_size = (off_t)n->size;
    st->st_rdev = (dev_t)n->rdev;
    st->st_nlink = S_ISDIR(n->mode) ? 2 + n->nsubdirs : n->owner->links;
    st->st_blksize = 4096;
    st->st_blocks = (blkcnt_t)((n->size + 511) / 512);
    st->st_mtim.tv_sec = n->mtime;
    st->st_mtim.tv_nsec = n->mtime_nsec;
    st->st_atim.tv_sec = n->atime;
    st->st_atim.tv_nsec = n->atime_nsec;
    st->st_ctim = st->st_mtim;
}

static void* fs_init(struct fuse_conn_info *conn, struct fuse_config *cfg) {
#ifdef FUSE_CAP_POSIX_ACL
    // Let the kernel enforce stored ACLs (system.posix_acl_* attributes)
    if (conn->capable & FUSE_CAP_POSIX_ACL) conn->want |= FUSE_CAP_POSIX_ACL;
#else
    (void)conn;
#endif
    cfg->use_ino = 1;
    cfg->kernel_cache = 1;          // the image never changes while mounted
    cfg->entry_timeout = 3600;
    cfg->attr_timeout = 3600;
    cfg->negative_timeout = 3600;
    return NULL;
}

static int fs_getattr(const char *path, struct stat *st, struct fuse_file_info *fi) {
    (void)fi;
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    fill_stat(n, st);
    return 0;
}

static int fs_readlink(const char *path, char *buf, size_t size) {
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    if (!S_ISLNK(n->mode) || size == 0) return -EINVAL;
    snprintf(buf, size, "%s", n->target);
    return 0;
}

static int fs_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset,
                      struct fuse_file_info *fi, enum fuse_readdir_flags flags) {
    (void)offset; (void)fi; (void)flags;
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    if (!S_ISDIR(n->mode)) return -ENOTDIR;
    filler(buf, ".", NULL, 0, 0);
    filler(buf, "..", NULL, 0, 0);
    for (uint32_t i = 0; i < n->nchildren; i++) {
        struct stat st;
        fill_stat(n->children[i], &st);
        if (filler(buf, n->children[i]->name, &st, 0, 0)) break;
    }
    return 0;
}

static int fs_open(const char *path, struct fuse_file_info *fi) {
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    if ((fi->flags & O_ACCMODE) != O_RDONLY) return -EROFS;
    if (S_ISDIR(n->mode)) return -EISDIR;
    fi->fh = (uint64_t)(uintptr_t)n;
    fi->keep_cache = 1;
    return 0;
}

static int fs_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
    mnode_t *n = fi ? (mnode_t*)(uintptr_t)fi->fh : mlookup(path);
    if (!n) return -ENOENT;
    if (!S_ISREG(n->mode) || offset < 0) return -EINVAL;
    uint64_t off = (uint64_t)offset;
    if (off >= n->size || size == 0) return 0;
    if (size > n->size - off) size = (size_t)(n->size - off);

    uint64_t pos = n->data_off + off;
    uint8_t *dst = (uint8_t*)buf;
    size_t left = size;
    uint32_t bs = g_img.h.block_size;
    while (left > 0) {
        uint32_t index = (uint32_t)(pos / bs);
        uint32_t in_block = (uint32_t)(pos % bs);
        uint32_t raw = block_raw_len(&g_img, index);
        size_t chunk = raw - in_block;
        if (chunk > left) chunk = left;

        // Shared cache first
        int hit = 0;
        pthread_mutex_lock(&g_lru_lock);
        for (uint32_t i = 0; i < g_lru_count; i++) {
            if (g_lru[i].index == (int64_t)index) {
                g_lru[i].stamp = ++g_lru_clock;
                memcpy(dst, g_lru[i].data + in_block, chunk);
                hit = 1;
                break;
            }
        }
        pthread_mutex_unlock(&g_lru_lock);

        if (!hit) {
            // Decode outside the lock, then publish the block for other threads
            block_cache_t *c = thread_cache();
            if (!c) return -ENOMEM;
            if (read_block(&g_img, index, c->raw, c->scratch, c->model) != 0) {
                fprintf(stderr, "claudex: corrupt data block in '%s'\n", n->path);
                return -EIO;
            }
            memcpy(dst, c->raw + in_block, chunk);

            pthread_mutex_lock(&g_lru_lock);
            lru_entry_t *victim = NULL;
            for (uint32_t i = 0; i < g_lru_count; i++) {
                if (g_lru[i].index == (int64_t)index) {
                    victim = NULL;      // another thread got there first
                    break;
                }
                if (!victim || g_lru[i].stamp < victim->stamp) victim = &g_lru[i];
            }
            if (victim) {
                memcpy(victim->data, c->raw, raw);
                victim->index = index;
                victim->stamp = ++g_lru_clock;
            }
            pthread_mutex_unlock(&g_lru_lock);
        }

        dst += chunk;
        pos += chunk;
        left -= chunk;
    }
    return (int)size;
}

static int fs_getxattr(const char *path, const char *name, char *value, size_t size) {
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    n = n->owner;   // hard links share one set of attributes
    const uint8_t *rec = n->xattrs;
    char rname[XATTR_NAME_MAX_LEN + 1];
    for (uint32_t i = 0; i < n->xattr_count; i++) {
        const uint8_t *v;
        uint32_t vlen;
        rec = xattr_next(rec, rname, &v, &vlen);
        if (strcmp(rname, name) != 0) continue;
        if (size == 0) return (int)vlen;
        if (size < vlen) return -ERANGE;
        memcpy(value, v, vlen);
        return (int)vlen;
    }
    return -ENODATA;
}

static int fs_listxattr(const char *path, char *list, size_t size) {
    mnode_t *n = mlookup(path);
    if (!n) return -ENOENT;
    n = n->owner;
    const uint8_t *rec = n->xattrs;
    char rname[XATTR_NAME_MAX_LEN + 1];
    size_t total = 0;
    for (uint32_t i = 0; i < n->xattr_count; i++) {
        const uint8_t *v;
        uint32_t vlen;
        rec = xattr_next(rec, rname, &v, &vlen);
        size_t len = strlen(rname) + 1;
        if (size > 0) {
            if (total + len > size) return -ERANGE;
            memcpy(list + total, rname, len);
        }
        total += len;
    }
    return (int)total;
}

static int fs_statfs(const char *path, struct statvfs *sv) {
    (void)path;
    memset(sv, 0, sizeof(*sv));
    sv->f_bsize = 4096;
    sv->f_frsize = 4096;
    sv->f_blocks = (g_img.h.image_size + 4095) / 4096;
    sv->f_files = g_node_count;
    sv->f_namemax = 255;
    sv->f_flag = ST_RDONLY;
    return 0;
}

static const struct fuse_operations fs_ops = {
    .init     = fs_init,
    .getattr  = fs_getattr,
    .readlink = fs_readlink,
    .readdir  = fs_readdir,
    .open     = fs_open,
    .read     = fs_read,
    .statfs   = fs_statfs,
    .getxattr = fs_getxattr,
    .listxattr = fs_listxattr,
};

static int cmd_mount(int argc, char **argv, char *prog) {
    // argv: "mount" <image> <mountpoint> [--rootfs] [fuse options...]
    if (argc < 3) {
        fprintf(stderr, "usage: mkfs.claudex mount <image> <mountpoint> [--rootfs] [-f] [-o options]\n");
        return 1;
    }
    int rootfs = 0;
    for (int i = 3; i < argc; i++) {
        if (strcmp(argv[i], "--rootfs") == 0) rootfs = 1;
    }

    if (open_or_die(&g_img, argv[1]) != 0) return 1;
    if (mkdir_p(argv[2], 0755) != 0) {
        fprintf(stderr, "claudex: cannot create mount point %s: %s\n", argv[2], strerror(errno));
        return 1;
    }
    if (build_mount_index() != 0) {
        fprintf(stderr, "claudex: cannot index image (out of memory?)\n");
        return 1;
    }
    if (pthread_key_create(&g_cache_key, free_thread_cache) != 0) return 1;

    g_lru_count = LRU_BYTES / g_img.h.block_size;
    if (g_lru_count < 8) g_lru_count = 8;
    g_lru = calloc(g_lru_count, sizeof(lru_entry_t));
    if (!g_lru) return 1;
    for (uint32_t i = 0; i < g_lru_count; i++) {
        g_lru[i].index = -1;
        g_lru[i].data = malloc(g_img.h.block_size);
        if (!g_lru[i].data) return 1;
    }

    if (rootfs) {
        /* Serving the root filesystem: systemd leaves processes whose name
         * starts with '@' running at shutdown, so / stays readable until the end */
        prog[0] = '@';
    }

    // fuse_main gets: program, mountpoint, user options, then our fixed options
    char **fargv = calloc((size_t)argc + 3, sizeof(char*));
    if (!fargv) return 1;
    int fargc = 0;
    fargv[fargc++] = prog;
    for (int i = 2; i < argc; i++) {
        if (strcmp(argv[i], "--rootfs") != 0) fargv[fargc++] = argv[i];
    }
    fargv[fargc++] = "-o";
    fargv[fargc++] = rootfs ? "ro,default_permissions,allow_other,suid,dev,fsname=claudex,subtype=claudex"
                            : "ro,default_permissions,fsname=claudex,subtype=claudex";

    if (!rootfs) {
        printf("Mounting %u entries from %s at %s (read-only)\n", g_node_count, argv[1], argv[2]);
        fflush(stdout);   // fuse_main forks into the background
    }
    int rc = fuse_main(fargc, fargv, &fs_ops, NULL);
    free(fargv);
    image_close(&g_img);
    return rc;
}

/* =====================================================================
 *  Boot support: mkinitcpio hook
 * ===================================================================== */

/* The hooks follow the arch/miso live-boot hooks: the 'arch' hook finds the
 * boot media (label=), sets up cow space, copytoram and the overlay root, and
 * calls _mount_root_overlayfs for each image in ${root}/ (default LiveOS).
 * The claudex hook comes after 'arch' in HOOKS, so its _mount_root_overlayfs
 * replaces the original: it mounts ${root}/root.claudex when present and
 * otherwise does exactly what the arch hook would with rootfs.img. */

// install/claudex: what goes into the initramfs
static const char initcpio_install[] =
    "#!/bin/bash\n"
    "\n"
    "build() {\n"
    "    add_module \"fuse\"\n"
    "    add_module \"overlay\"\n"
    "    add_module \"loop\"\n"
    "\n"
    "    add_runscript\n"
    "\n"
    "    add_binary mkfs.claudex\n"
    "}\n"
    "\n"
    "help() {\n"
    "    cat <<HELPEOF\n"
    "Boots the live system from a claudex image. Works with the arch hook and must\n"
    "come after it in HOOKS: if <root>/root.claudex exists on the boot media\n"
    "(root= defaults to LiveOS) it is mounted with mkfs.claudex instead of\n"
    "rootfs.img. All arch hook options (label=, copytoram=y, cow_*) still apply.\n"
    "HELPEOF\n"
    "}\n"
    "\n"
    "# vim: set ft=sh ts=4 sw=4 et:\n";

// hooks/claudex: runs inside the initramfs at boot
static const char initcpio_hook[] =
    "# args: /path/to/image_file, mountpoint\n"
    "_mnt_claudex() {\n"
    "    local img=\"${1}\"\n"
    "    local mnt=\"${2}\"\n"
    "    local img_fullname=\"${img##*/}\"\n"
    "    local oper=$( [[ -n \"${ip}\" && -n \"${miso_http_srv}\" ]] && echo \"mv\" || echo \"cp\" )\n"
    "\n"
    "    if [[ \"${copytoram}\" == \"y\" ]]; then\n"
    "        msg -n \":: Copying claudex image to RAM...\"\n"
    "        if ! \"${oper}\" \"${img}\" \"${cp2ram}/${img_fullname}\" ; then\n"
    "            echo \"ERROR: while copy '${img}' to '${cp2ram}/${img_fullname}'\"\n"
    "            launch_interactive_shell\n"
    "        fi\n"
    "        img=\"${cp2ram}/${img_fullname}\"\n"
    "        msg \"done.\"\n"
    "    fi\n"
    "\n"
    "    mkdir -p \"${mnt}\"\n"
    "\n"
    "    msg \":: Mounting '${img}' to '${mnt}'\"\n"
    "\n"
    "    if mkfs.claudex mount \"${img}\" \"${mnt}\" --rootfs; then\n"
    "        msg \":: Image '${img}' mounted successfully.\"\n"
    "    else\n"
    "        echo \"ERROR; Failed to mount '${img}'\"\n"
    "        echo \"   Falling back to interactive prompt\"\n"
    "        echo \"   You can try to fix the problem manually, log out when you are finished\"\n"
    "        launch_interactive_shell\n"
    "    fi\n"
    "}\n"
    "\n"
    "# Replaces the arch hook's version: root.claudex is used when present,\n"
    "# otherwise the image is handled exactly as before.\n"
    "_mount_root_overlayfs() {\n"
    "    local sfs=\"${1}\"\n"
    "    local src=\"${bootmnt}/${root}\"\n"
    "    local dest_sfs=\"${live_root}/sfs\"\n"
    "    local dest_img=\"${live_root}/img\"\n"
    "    local cx=\"${src}/${sfs}.claudex\"\n"
    "\n"
    "    [[ \"${sfs}\" == \"rootfs\" ]] && cx=\"${src}/root.claudex\"\n"
    "\n"
    "    if [[ -f \"${cx}\" ]]; then\n"
    "        _mnt_claudex \"${cx}\" \"${live_root}/claudex/${sfs}\"\n"
    "        lower_dir=$(_gen_arg \"${live_root}/claudex/${sfs}\")\n"
    "    elif [[ -f \"${src}/${sfs}.img\" ]]; then\n"
    "        _mnt_sfs \"${src}/${sfs}.img\" \"${dest_sfs}/${sfs}\"\n"
    "        local find_img=\"${dest_sfs}/${sfs}/LiveOS/${sfs}.img\"\n"
    "        if [[ -f \"${find_img}\" ]]; then\n"
    "            mkdir -p ${dest_img}\n"
    "            lower_dir=$(_gen_arg \"${dest_img}/${sfs}\")\n"
    "            _mnt_dmsnapshot \"${find_img}\" \"${dest_img}/${sfs}\"\n"
    "        else\n"
    "            lower_dir=$(_gen_arg \"${dest_sfs}/${sfs}\")\n"
    "        fi\n"
    "    fi\n"
    "}\n"
    "\n"
    "# vim:ft=sh:ts=4:sw=4:et:\n";

// mkinitcpio config for the ISO's initramfs. claudex must come after arch.
static const char initcpio_conf[] =
    "# mkinitcpio config for booting a claudex image (written by 'mkfs.claudex initcpio')\n"
    "# Build the initramfs with:\n"
    "#   mkinitcpio -c <this file> -k /boot/vmlinuz-linux -g initramfs-linux.img\n"
    "\n"
    "MODULES=(loop btrfs dm-snapshot fuse overlay isofs)\n"
    "\n"
    "HOOKS=(base udev arch_shutdown arch arch_loop_mnt arch_kms\n"
    "        modconf block filesystems keyboard keymap claudex)\n"
    "\n"
    "COMPRESSION=\"zstd\"\n"
    "\n"
    "COMPRESSION_OPTIONS=(--ultra -22)\n";

static int write_file_text(const char *path, const char *text) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
    if (fd < 0) return -1;
    int rc = write_all(fd, text, strlen(text));
    if (close(fd) != 0) rc = -1;
    return rc;
}

static int cmd_initcpio(const char *dir) {
    char sub[MAX_PATH_LEN], path[MAX_PATH_LEN];
    const char *names[2] = { "install", "hooks" };
    const char *texts[2] = { initcpio_install, initcpio_hook };

    for (int i = 0; i < 2; i++) {
        snprintf(sub, sizeof(sub), "%s/%s", dir, names[i]);
        if (mkdir_p(sub, 0755) != 0) goto fail;
        snprintf(path, sizeof(path), "%s/claudex", sub);
        if (write_file_text(path, texts[i]) != 0) goto fail;
        printf("\033[32mWrote %s\033[0m\n", path);
    }

    // mkinitcpio.conf goes in the current directory. Never overwrite one that
    // may have been edited since.
    snprintf(path, sizeof(path), "mkinitcpio.conf");
    struct stat st;
    if (lstat(path, &st) == 0) {
        printf("\033[33mKept existing ./%s (delete it to regenerate)\033[0m\n", path);
    } else {
        if (write_file_text(path, initcpio_conf) != 0) {
            fprintf(stderr, "\033[31mError: cannot write ./mkinitcpio.conf: %s\033[0m\n", strerror(errno));
            return 1;
        }
        printf("\033[32mWrote ./%s\033[0m\n", path);
    }

    printf("\033[32mBuild the ISO's initramfs with ./mkinitcpio.conf (claudex after arch in HOOKS) and put\n"
           "the image on the boot media as <root>/root.claudex (root= defaults to LiveOS).\n"
           "mkfs.claudex must be in PATH when mkinitcpio runs (sudo make install).\033[0m\n");
    return 0;

fail:
    fprintf(stderr, "\033[31mError: cannot write to %s: %s\033[0m\n", dir, strerror(errno));
    return 1;
}

/* =====================================================================
 *  main
 * ===================================================================== */

static void usage(void) {
    printf(
        "mkfs.claudex - compressed, mountable filesystem images\n\n"
        "  mkfs.claudex create [options] <source-dir> <image>\n"
        "      -l <0-9>               compression level (default 9 = maximum; 0 = store only)\n"
        "      -b <size>              block size, e.g. 256K, 1M, 4M, 16M (default 1M; bigger = smaller\n"
        "                             image, slower random reads when mounted)\n"
        "      -T <n>                 threads (default: all CPUs)\n"
        "      --exclude=<path>       skip a path or pattern (in addition to the defaults)\n"
        "      --no-default-excludes  don't skip /proc /sys /dev /run /tmp /mnt /media, caches, logs,\n"
        "                             the pacman package cache, /etc/fstab, root.claudex or backup.claudex\n"
        "      --no-dedup             don't look for identical files\n"
        "      -q                     no progress bar\n"
        "  mkfs.claudex mount <image> <dir> [-f] [-o opts]   mount read-only (unmount: fusermount3 -u <dir>)\n"
        "      --rootfs               serve as the root filesystem at boot (used by the initcpio hook)\n"
        "  mkfs.claudex extract <image> [dest] [-v]          extract (default: current directory)\n"
        "  mkfs.claudex test <image>                         verify every file\n"
        "  mkfs.claudex list <image>                         list contents\n"
        "  mkfs.claudex info <image>                         image statistics\n"
        "  mkfs.claudex initcpio [dir]                       install the boot hook for mkinitcpio\n"
        "                                                    (default dir: /etc/initcpio) and write\n"
        "                                                    ./mkinitcpio.conf\n");
}

int main(int argc, char **argv) {
    if (argc < 2 || strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "help") == 0) {
        usage();
        return argc < 2 ? 1 : 0;
    }
    const char *cmd = argv[1];

    if (strcmp(cmd, "create") == 0 || strcmp(cmd, "c") == 0) {
        return cmd_create(argc - 1, argv + 1);
    }
    if (strcmp(cmd, "mount") == 0 || strcmp(cmd, "m") == 0) {
        return cmd_mount(argc - 1, argv + 1, argv[0]);
    }
    if (strcmp(cmd, "extract") == 0 || strcmp(cmd, "x") == 0) {
        const char *image = NULL, *dest = NULL;
        int verbose = 0;
        for (int i = 2; i < argc; i++) {
            if (strcmp(argv[i], "-v") == 0) verbose = 1;
            else if (!image) image = argv[i];
            else if (!dest) dest = argv[i];
        }
        if (!image) {
            usage();
            return 1;
        }
        return cmd_extract(image, dest ? dest : ".", verbose);
    }
    if ((strcmp(cmd, "test") == 0 || strcmp(cmd, "t") == 0) && argc >= 3) return cmd_extract(argv[2], NULL, 0);
    if ((strcmp(cmd, "list") == 0 || strcmp(cmd, "l") == 0) && argc >= 3) return cmd_list(argv[2]);
    if (strcmp(cmd, "info") == 0 && argc >= 3) return cmd_info(argv[2]);
    if (strcmp(cmd, "initcpio") == 0) return cmd_initcpio(argc >= 3 ? argv[2] : "/etc/initcpio");

    usage();
    return 1;
}
