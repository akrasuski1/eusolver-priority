CFLAGS=-std=c11 -O3 -Wall -pedantic
LDFLAGS=-O3
CC=gcc
LD=ld
SOLIB=./lib/libeusolver.so
ARLIB=./lib/libeusolver.a
PYLIB=./lib/eusolver.pyc

SRCS=./src/BitSet.c

.PHONY: all
.PHONY: clean

default: all

all: $(SOLIB) $(ARLIB) $(PYLIB)

$(SOLIB): src/BitSet-pic.o
	gcc -shared -fPIC -o $@ src/BitSet-pic.o

$(ARLIB): src/BitSet.o
	ar rcs $@ src/BitSet.o

src/%-pic.o: src/%.c
	$(CC) $(CFLAGS) -fPIC -c $< -o $@

src/%.o: src/%.c
	$(CC) $(CFLAGS) -c $< -o $@

$(PYLIB): src/eusolver.py
	python3 -m py_compile $<
	cp src/eusolver.py ./lib

clean:
	rm -rf src/BitSet.o lib/*
