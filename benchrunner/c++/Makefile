CFILES   = $(wildcard *.c)
OBJFILES = $(CFILES:.c=.o)
OUT      = cbench.exe

USECLANG    := 0
DEBUG       := 0
CILK        := 0

ifeq ($(CILK), 1)
	ifeq ($(USECLANG), 0)
		$(error cilk can only be used with an opencilk compiler!)
	endif
endif

OpenCILK_CLANG       := clang-16
OpenCILK_CLANG_FLAGS := -std=gnu11 -DCILK -fopencilk -fPIC
CLANG       := clang++
CLANG_FLAGS := -std=c++11 -lm -fPIC
GCC         := g++
GCC_FLAGS   := -std=c++11 -lm -fPIC

CC     := $(GCC)
CFLAGS := $(GCC_FLAGS)
CDEBUG := -DCBENCH_DEBUG -O0 -g

CFLAGS += -Wall -Wextra -Wpedantic -flto

ifeq ($(USECLANG), 1)
	CC     = $(CLANG)
	CFLAGS = $(CLANG_FLAGS)
	LFLAGS := -fuse-ld=lld
endif

ifeq ($(CILK), 1)
	ifeq ($(USECLANG), 1)
		CC     = $(OpenCILK_CLANG)
		CFLAGS = $(OpenCILK_CLANG_FLAGS)
		LFLAGS := -fuse-ld=lld
	endif
endif

ifeq ($(DEBUG), 1)
	CFLAGS += $(CDEBUG)
else
	CFLAGS += -O3
endif

all: $(OUT)

$(OUT): $(OBJFILES)
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $^

clean:
	rm -f $(OBJFILES) $(OUT)

.PHONY: clean
