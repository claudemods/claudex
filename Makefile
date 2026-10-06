CC = gcc
CFLAGS = -O3 -std=gnu11 -Wall -Wextra -pthread
FUSE = $(shell pkg-config --cflags --libs fuse3)

mkfs.claudex: claudex.c
	$(CC) $(CFLAGS) -o $@ claudex.c $(FUSE)

install: mkfs.claudex
	install -m 755 mkfs.claudex /usr/local/bin/

clean:
	rm -f mkfs.claudex

.PHONY: install clean
