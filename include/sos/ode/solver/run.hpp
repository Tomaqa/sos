#pragma once

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        template <typename S>
        class Solver::Run {
        public:
            int run(int argc, const char* argv[]);
        private:
            using Solver_ptr = unique_ptr<S>;

            static Solver_ptr new_solver(S&& solver_);

            Solver_ptr _solver_ptr;
        };
    }
}

#include "ode/solver/run.tpp"
