#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        template <typename S>
        class Solver::Run : public Util::Run {
        public:
            using Util::Run::Run;
        protected:
            virtual void do_stuff() override;
        };
    }
}

#include "ode/solver/run.tpp"
