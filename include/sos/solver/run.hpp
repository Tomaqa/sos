#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "solver.hpp"

namespace SOS {
    template <typename OSolver>
    class Solver<OSolver>::Run : public Util::Run {
    public:
        using Util::Run::Run;
    protected:
        virtual void do_stuff() override;
    };
}

#include "solver/run.tpp"
