# SOS: SMT+ODE Solver

This work is the result of diploma thesis at FIT-CTU in Prague.

## Announcement

This software is only a prototype,
do not expect user-friendly interface and bug-free usage.
Users are welcome to use this software, and asked to report discovered bugs to GitHub.

## Download

[GitHub](https://github.com/Tomaqa/sos) repository

## Installation

Installation itself is not implemented yet, only local build.

To build, run:
```
make
```

### Dependencies
* C++, STL, POSIX
* Boost
* [z3 prover](https://github.com/Z3Prover/z3)
* gnuplot [optional]

To avoid using Boost, one must delete all source files related to odeint
and use only `euler` equivalents.

To use different SMT solver, one must manually edit source file
`src/sos/smt/solver.cpp` with line containing `execlp`.
There is a commented line with [CVC4](https://github.com/CVC4/CVC4).

## Usage

Run `bin/sos_odeint -h` and follow instructions.

`bin/sos_euler` is reserved chiefly
for cases when Boost library is not present.

## Documentation

Source files are not documented yet.

Only thesis text in Czech languge is present so far
at `doc/articles/thesis/text`.

## Development

Source codes are written in C++14 in Stroustrup code style.

When source files structure changes,
one needs to manually remove the tail of `Makefile`
and run `tools/dev/deps.sh`.
Calling `make clean` is also likely to be appropriate.

## Contributing

Bug reports and pull requests are welcome on GitHub at
https://github.com/Tomaqa/sos.

## License

The tool is available as open source under the terms of the [MIT License](https://opensource.org/licenses/MIT).
