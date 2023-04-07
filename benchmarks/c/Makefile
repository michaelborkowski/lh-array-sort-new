CFILES   = $(wildcard *.c)
OBJFILES = $(CFILES:.c=.o)
OUT      = cbench.exe

CLANG       := /scratch/ckoparka/opencilk/bin/clang
CLANG_FLAGS := -std=gnu11 -fopencilk
GCC         := gcc-7
GCC_FLAGS   := -std=gnu11 -lm -fcilkplus

CC     := $(GCC)
CFLAGS := $(GCC_FLAGS)

ifeq ($(USECLANG), 1)
	CC     = $(CLANG)
	CFLAGS = $(CLANG_FLAGS)
	LFLAGS := -fuse-ld=lld
endif

CFLAGS += -Wall -Wextra -Wpedantic -O3 -flto
CDEBUG := -DCBENCH_DEBUG -O0 -g

ifeq ($(DEBUG), 1)
	CFLAGS += $(CDEBUG)
endif

$(OUT): $(OBJFILES)
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $^

clean:
	rm -f $(OBJFILES) $(OUT)

.PHONY: clean
