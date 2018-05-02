#!/bin/sh
find src/ -type f -exec g++ -c -std=c++14 -I include/sos -I include/test -MM {} -MT {} \; | sed 's|^[^/]*/\([^.]*\)\.[^:]*:|build/\1.o:|' >> Makefile
