#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "expr/eval.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval<Arg>::Run : public Util::Run {
    public:
        using Util::Run::Run;
    protected:
        virtual void do_stuff() override;
    };
}

#include "expr/eval/run.tpp"
