#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "smt/solver.hpp"

namespace SOS {
    namespace SMT {
        class Solver::Run : public Util::Run {
        public:
            using Util::Run::Run;
        protected:
            virtual void do_stuff() override;
        };
    }
}
