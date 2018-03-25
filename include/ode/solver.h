#ifndef ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
#define ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430

#include "ode.h"

namespace SOS {
    namespace ODE {
        class Solver {
        public:
            using Ode_spec = string;
            using Ode_id = int;

            struct Context;

            Solver() = default;
            ~Solver() = default;
            Solver(const Solver& rhs) = delete;
            Solver& operator =(const Solver& rhs) = delete;

            void set_step_size(Time step_size) { _step_size = step_size; }
            virtual State solve(const Context& context) = 0;
            State solve(const string& input);
        protected:
            Time _step_size{1.0};
        };

        struct Solver::Context {
            Context(Ode_id ode_id,
                    const Interval<Time>& t_bounds,
                    State x_init)
            : _ode_id(ode_id),
              _t_bounds(t_bounds), _x_init(x_init)
            {}

            Ode_id _ode_id;
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
