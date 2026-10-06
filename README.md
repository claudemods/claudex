# claudex

![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)

A compressed, mountable, bootable filesystem image format for Linux, with its own compression engine.

`mkfs.claudex` packs a whole directory tree, or a whole Arch Linux system, into a single `.claudex` image file. You can then:

- **mount** it read-only through FUSE and browse it like a normal folder
- **boot** it as a live root filesystem from an ISO or USB stick, using the included mkinitcpio hook
- **extract** or **verify** it at any time

Everything, including the compressor, is in one C file. No zlib, zstd or xz is used.

---

## Features

- **Custom compressor (CX).** LZ77 matching with an adaptive range coder. Literals, lengths and distances are each predicted from context.
- **Optimal parsing** at levels 8–9. The compressor picks the cheapest combination of matches over the next few thousand bytes instead of always taking the longest one.
- **x86 filter.** In blocks of program and library code, call addresses are made absolute so repeated calls compress better.
- **Solid packing.** All file data is concatenated into one stream, so small files compress together instead of one by one.
- **Similar files grouped.** Files are ordered by extension so related content sits next to each other.
- **Deduplication.** Identical files are stored once. Matches are confirmed byte by byte, never by hash alone.
- **Hard links preserved.** Hard-linked names are stored once and restored as real hard links. When mounted they share one inode and the correct link count.
- **Exact permissions and metadata.** The image keeps:
  - owner, group and mode, including setuid, setgid and sticky bits
  - every extended attribute: ACLs, file capabilities and security labels
  - modification and access times to the nanosecond

  These are restored on extract and reported when mounted or booted, with ACLs enforced.
- **Read-only on your system.** Source files are only ever read, and are opened with `O_NOATIME` so even their access times stay unchanged.
- **Multithreaded.** Every block is compressed in parallel, including blocks of a single huge file.
- **Random access.** Data is split into independent blocks, so reading one file only decompresses the blocks it covers.
- **Integrity checks.** CRC-32 covers every file, the block table and the metadata. Every compressed block is decompressed and compared with the original before it is written.
- **Bootable.** The `--rootfs` mount mode plus a mkinitcpio hook let a `.claudex` image act as the root filesystem of a live system.
- **Sensible default excludes** for system images: `/proc`, `/sys`, caches, logs, the pacman package cache, and so on.
- **Progress bar on a single line,** with a spinner, that adapts to the terminal width.

---

## Requirements

- Linux
- `gcc`, `make`, `pkg-config`
- `fuse3`, used for mounting and booting

On Arch Linux:

```bash
sudo pacman -S --needed base-devel fuse3
```

---

## Building

```bash
make
sudo make install      # installs to /usr/local/bin/mkfs.claudex
```

---

## Usage

### Create an image

```bash
mkfs.claudex create [options] <source-dir> <image>
```

| Option | Description |
|---|---|
| `-l <0-9>` | Compression level. Default `9` (maximum, optimal parsing); `0` = store only. Levels 1–7 are faster. |
| `-b <size>` | Block size, e.g. `256K`, `1M`, `4M`, `16M`. Default `1M`. Bigger means a smaller image but slower random reads when mounted. |
| `-T <n>` | Number of threads. Default: all CPUs. |
| `--exclude=<path>` | Skip a path or pattern (`*`, `?`, `[...]`), in addition to the defaults. Can be repeated. |
| `--no-default-excludes` | Don't apply the default excludes listed below. |
| `--no-dedup` | Don't look for identical files. |
| `-q` | No progress bar. |

If `<image>` is an existing folder, the image is written inside it as `backup.claudex`. Otherwise `.claudex` is added to the name if it's missing. Any missing parent folders are created.

Examples:

```bash
# Back up a home folder
mkfs.claudex create /home/test /home/test/pictures/backup

# Whole system, maximum compression, 4 MiB blocks
sudo mkfs.claudex create -b 4M / /mnt/storage/root.claudex

# Faster, with extra excludes
mkfs.claudex create -l 6 --exclude=/home/test/Downloads --exclude='/home/*/Videos' /home home.claudex
```

### Mount an image

```bash
mkfs.claudex mount <image> <mountpoint> [-f] [-o options]
fusermount3 -u <mountpoint>        # unmount
```

The mount is read-only. File owners and permissions are enforced as stored. `-f` keeps it in the foreground.

### Extract, verify, list, inspect

```bash
sudo mkfs.claudex extract <image> [destination] [-v]   # default destination: current folder; sudo restores owners/capabilities
mkfs.claudex test <image>                         # verify every file's checksum
mkfs.claudex list <image>                         # ls -l style listing
mkfs.claudex info <image>                         # sizes, ratio, block statistics
```

---

## Default excludes

These are skipped unless you pass `--no-default-excludes`. Each path is only excluded when it lies *inside* the folder you're packing, so packing `/tmp/project` itself still works.

| Path | Why |
|---|---|
| `/proc` `/sys` `/dev` `/run` | Virtual filesystems |
| `/tmp` `/var/tmp` | Temporary files |
| `/mnt` `/media` | Other mounted drives |
| `/lost+found` `/swapfile` `/swap.img` | Not system data |
| `/var/cache/pacman/pkg` | Downloaded packages (already compressed, often several GB) |
| `/home/*/.cache` `/root/.cache` | Application caches |
| `/var/log/journal` `/var/lib/systemd/coredump` | Logs and crash dumps |
| `/etc/fstab` | Lists the original machine's disks, which won't exist when the image is booted elsewhere |
| any file named `backup.claudex` | Older images |

The image being written is never packed into itself.

---

## Booting a live system from an image

`mkfs.claudex` can serve an image as the root filesystem of a live system. A writable RAM layer (overlayfs) goes on top, the same idea as the official Arch ISO's `airootfs`.

**1. Create the image of your system**

```bash
sudo mkfs.claudex create / /path/to/root.claudex
```

Recreate the image after kernel updates. The live system loads kernel modules from the image, so they must match the kernel on the ISO.

**2. Install the mkinitcpio hook**

```bash
sudo mkfs.claudex initcpio                         # writes /etc/initcpio/{install,hooks}/claudex
# or into your ISO profile:
mkfs.claudex initcpio myprofile/airootfs/etc/initcpio
```

**3. Build the ISO's initramfs with the hook**

```
HOOKS=(base udev modconf block filesystems keyboard claudex)
```

Don't use `autodetect`. It would limit the initramfs to the build machine's hardware. `mkfs.claudex` must be in `PATH` when mkinitcpio runs.

**4. Kernel parameters**

| Parameter | Description |
|---|---|
| `claudex=<path>` | Path of the image on the boot media, e.g. `claudex=/arch/root.claudex` (required) |
| `claudex_dev=<device>` | Device holding the image. Default: search every disk and optical drive. |
| `claudex_copytoram=y` | Copy the image into RAM before mounting (needs more RAM than the image size) |
| `cow_spacesize=<size>` | Size of the writable RAM layer, default `75%` |

At boot the hook:

1. finds the boot media
2. mounts the image with `mkfs.claudex mount --rootfs`
3. layers a tmpfs on top with overlayfs

The image is used exactly as packed. `/etc/fstab` is left out by the default excludes.

The FUSE process names itself with a leading `@`, so systemd leaves it running until the very end of shutdown.

---

## How the compression works

1. **Scan.** The source tree is walked and excludes are applied.
2. **Order.** Regular files are sorted by extension, then name, so similar data ends up next to each other.
3. **Deduplicate.** Files that share a size are checksummed in parallel, and checksum matches are confirmed byte by byte. Duplicates point at the first copy.
4. **Stream.** File contents are concatenated into one data stream and cut into fixed-size blocks.
5. **Compress.** Worker threads compress the blocks in parallel:
   - Blocks that look like x86 code first go through the call-address filter.
   - The CX encoder (LZ77 plus range coder) compresses the block. At levels 8–9 it uses optimal parsing.
   - Every block is decompressed and compared with the original. If a block doesn't shrink, or the check fails, it is stored raw.
6. **Write.** Blocks are written strictly in order, followed by the block table, the compressed metadata (paths, modes, owners, times, symlink targets) and a footer.

---

## Image format (version 6)

All integers are little-endian.

```
header       96 bytes   magic "CLDX", version, level, block size, counts,
                        offsets, sizes, CRC-32 of the header
data blocks             compressed (CX / CX+x86) or stored blocks of the data stream
block table             per block: offset (u64), stored length (u32), type (u8), padding
metadata                chunks {raw_len u32, stored_len u32, type u8, data}
footer       8 bytes    "CLDE" + entry count
```

Each metadata entry holds a path, mode, uid, gid, mtime and atime (each with nanoseconds), and its extended attributes. Regular files add data offset, size, CRC-32, and a hard-link reference to an earlier entry (if any). Symlinks add a target. Device nodes add rdev. Parent directories always come before their contents.

---

## Limitations

- Restoring owners, file capabilities and `trusted.*` attributes needs root. Run `sudo mkfs.claudex extract` for an exact copy. Without root, extract warns about anything it couldn't restore and exits with code 2.
- The kernel always sets a file's change time (ctime) and inode number itself, so those can't be restored.
- Inode flags set with `chattr` (immutable, append-only, no-COW) are not stored.
- Images are read-only. Rebuild to change contents.
- x86 filtering only targets x86/x86-64 code. Other architectures still compress, just without the filter.
- Maximum block size is 64 MiB. Maximum path length is 8191 bytes.

---

## Project layout

```
claudex.c    the whole program: compressor, image writer/reader, FUSE driver, boot hook
Makefile     build / install
LICENSE      MIT license
```

---

## License

MIT. See [LICENSE](LICENSE).
