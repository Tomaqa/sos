#!/bin/sh
find src/ -type f -exec g++ -c -std=c++14 -I include -MM {} -MT {} \; | sed 's|^[^/]*/\([^.]*\)\.[^:]*:|build/\1.o:|' >> Makefile
