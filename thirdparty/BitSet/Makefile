CFLAGS=-std=c11 -O3 -Wall -pedantic
LDFLAGS=-O3
CC=gcc
LD=ld
SOLIB=./lib/libbitset.so
ARLIB=./lib/libbitset.a
PYLIB=./lib/bitset.pyc

.PHONY: all
.PHONY: clean

default: all

all: $(SOLIB) $(ARLIB) $(PYLIB)

$(SOLIB): src/BitSet-pic.o
	gcc -shared -fPIC -o $@ src/BitSet-pic.o

$(ARLIB): src/BitSet.o
	ar rcs $@ src/BitSet.o

src/BitSet-pic.o: src/BitSet.c src/BitSet.h
	$(CC) $(CFLAGS) -fPIC -c src/BitSet.c -o $@

src/BitSet.o: src/BitSet.c src/BitSet.h
	$(CC) $(CFLAGS) -c src/BitSet.c -o $@

$(PYLIB): src/bitset.py
	python3 -m py_compile src/bitset.py
	cp src/bitset.py ./lib

clean:
	rm -rf src/BitSet.o src/BitSet-pic.o lib/* src/__pycache__
