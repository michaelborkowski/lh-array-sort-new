CFILES   = $(wildcard *.c)
OBJFILES = $(CFILES:.c=.o)
OUT      = cbench.exe

CLANG       := clang-14
CLANG_FLAGS := -std=gnu11 -fopencilk
GCC         := gcc-7
GCC_FLAGS   := -std=gnu11 -lm -fcilkplus

CC     := $(GCC)
CFLAGS := $(GCC_FLAGS)
CDEBUG := -DCBENCH_DEBUG -O0 -g

CFLAGS += -Wall -Wextra -Wpedantic -flto

ifeq ($(USECLANG), 1)
	CC     = $(CLANG)
	CFLAGS = $(CLANG_FLAGS)
	LFLAGS := -fuse-ld=lld
endif

ifeq ($(DEBUG), 1)
	CFLAGS += $(CDEBUG)
else
	CFLAGS += -O3
endif

$(OUT): $(OBJFILES)
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $^

clean:
	rm -f $(OBJFILES) $(OUT)

.PHONY: clean
