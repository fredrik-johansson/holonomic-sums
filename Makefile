# Build against an installed FLINT 3 (headers in $(FLINT_PREFIX)/include/flint, library in $(FLINT_PREFIX)/lib).
FLINT_PREFIX ?= /usr/local
CC ?= cc
CFLAGS ?= -O2 -Wall -Wno-unused-function
CPPFLAGS += -I$(FLINT_PREFIX)/include
LDFLAGS += -L$(FLINT_PREFIX)/lib -Wl,-rpath,$(FLINT_PREFIX)/lib -L/home/fredrik/src/flint
LDLIBS += -lflint -lgmp -lmpfr -lm -lpthread

SRC = src/main.c src/engine.c src/refs.c src/logsums.c src/vortex.c src/hardy_littlewood.c
OBJ = $(SRC:.c=.o)

holsum: $(OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LDLIBS)

src/%.o: src/%.c src/engine.h src/constants.h
	$(CC) $(CFLAGS) $(CPPFLAGS) -c -o $@ $<

clean:
	rm -f holsum $(OBJ)

.PHONY: clean
