# Build holsum against FLINT 3, either
#   make FLINT_DIR=/path/to/flint          a FLINT source tree built in place (libflint in the
#                                          top directory, headers in build/include/flint), or
#   make FLINT_PREFIX=/path/to/install     an installed FLINT (default /usr/local).
# Extra paths, for example for GMP and MPFR, can be added with CPPFLAGS=-I... and LDFLAGS=-L...
CC ?= cc
CFLAGS ?= -O2 -Wall -Wno-unused-function
LDLIBS += -lflint -lgmp -lmpfr -lm -lpthread

ifdef FLINT_DIR
FLINT_LIBDIR := $(abspath $(FLINT_DIR))
CPPFLAGS += -I$(FLINT_LIBDIR)/build/include
else
FLINT_PREFIX ?= /usr/local
FLINT_LIBDIR := $(FLINT_PREFIX)/lib
CPPFLAGS += -I$(FLINT_PREFIX)/include
endif
LDFLAGS += -L$(FLINT_LIBDIR) -Wl,-rpath,$(FLINT_LIBDIR)

SRC = src/main.c src/engine.c src/refs.c src/logsums.c src/vortex.c src/hardy_littlewood.c src/somos.c src/expsqrt.c src/khinchin.c src/tsys.c src/theodorus.c src/sphere.c
OBJ = $(SRC:.c=.o)

holsum: $(OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LDLIBS)

src/%.o: src/%.c src/engine.h src/constants.h src/tsys.h
	$(CC) $(CFLAGS) $(CPPFLAGS) -c -o $@ $<

clean:
	rm -f holsum $(OBJ)

.PHONY: clean
