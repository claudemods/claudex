CC = gcc
CFLAGS = -O3 -std=gnu11 -Wall -Wextra -pthread
FUSE = $(shell pkg-config --cflags --libs fuse3)

claudex: claudex.c
	$(CC) $(CFLAGS) -o $@ claudex.c $(FUSE)

install: claudex
	install -m 755 claudex /usr/local/bin/

clean:
	rm -f claudex

.PHONY: install clean
