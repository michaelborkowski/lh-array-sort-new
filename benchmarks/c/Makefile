CFILES   = $(wildcard *.c)
OBJFILES = $(CFILES:.c=.o)
OUT      = cbench.exe

CLANG       := ~/chai/opencilk/bin/clang
CLANG_FLAGS := -std=c11 -fuse-ld=lld -fopencilk
GCC         := gcc
GCC_FLAGS   := -std=gnu11 -lm -fcilkplus

CC     := $(GCC)
CFLAGS := $(GCC_FLAGS)
CFLAGS += -Wall -Wextra -Wpedantic -O3 -flto -fwhole-program
CDEBUG := -DCBENCH_DEBUG -O0 -g


$(OUT): $(OBJFILES)
ifeq ($(DEBUG), 1)
	$(CC) $(CFLAGS) $(CDEBUG) -o $@ $^
else
	$(CC) $(CFLAGS) -o $@ $^
endif


%.o: %.c
ifeq ($(DEBUG), 1)
	$(CC) $(CFLAGS) $(CDEBUG) -c -o $@ $^
else
	$(CC) $(CFLAGS) -c -o $@ $^
endif


clean:
	rm -f $(OBJFILES) $(OUT)

.PHONY: clean
