CFILES   = $(wildcard *.c)
OBJFILES = $(CFILES:.c=.o)
OUT      = cbench.exe

CC = gcc
CFLAGS = -std=gnu11 -Wall -Wextra -Wpedantic -O3 -flto -fwhole-program -lm
CDEBUG = -DCBENCH_DEBUG -O0 -g

$(OUT): $(OBJFILES)
ifdef DEBUG
	$(CC) $(CFLAGS) $(CDEBUG) -o $@ $^
else
	$(CC) $(CFLAGS) -o $@ $^
endif

%.o: %.c
ifdef DEBUG
	$(CC) $(CFLAGS) $(CDEBUG) -c -o $@ $^
else
	$(CC) $(CFLAGS) -c -o $@ $^
endif

clean:
	rm -f $(OBJFILES) $(OUT)

.PHONY: clean
