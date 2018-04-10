#pragma once

#include "sos.hpp"
#include "expr/eval.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval<Arg>::Run {
    public:
        int run(int argc, const char* argv[]);
    private:
        Expr _expr;
        Eval<Arg> _eval;
    };
}

#include "expr/eval/run.tpp"
