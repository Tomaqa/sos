#ifndef ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
#define ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430

#include "ode.h"

namespace SOS {
    namespace ODE {
        class Solver {
        public:
            using Dt_spec = string;
            using Ode_spec = vector<Dt_spec>;
            using Odes_spec = vector<Ode_spec>;
            using Dt_id = int;
            using Ode_id = int;

            struct Context;

            Solver(Odes_spec&& odes_spec) : _odes_spec(odes_spec) { }
            Solver(Ode_spec&& ode_spec) : _odes_spec{ode_spec} { }
            ~Solver() = default;
            Solver(const Solver& rhs) = delete;
            Solver& operator =(const Solver& rhs) = delete;
            Solver(Solver&& rhs) = default;
            Solver& operator =(Solver&& rhs) = default;

            void set_step_size(Time step_size) { _step_size = step_size; }
            virtual State solve(Context&& context) const = 0;
            State solve(const string& input) const;
        protected:
            Odes_spec _odes_spec;
            Time _step_size{1.0};

            const Ode_spec& ode_spec(Ode_id ode_id) const
                { return _odes_spec[ode_id]; }
            void eval_ode(Ode_id ode_id, State& dx, const State& x, Time t) const;
            State eval_ode(Ode_id ode_id, const State& x, Time t) const
                { State dx; eval_ode(ode_id, dx, x, t); return dx; }
            const Dt_spec& dt_spec(const Ode_spec& ode_spec, Dt_id dt_id) const
                { return ode_spec[dt_id]; }
            Value eval_dt(const Ode_spec& ode_spec, Dt_id dt_id,
                          const State& x, Time t) const;
        };

        struct Solver::Context {
            Context(Ode_id ode_id,
                    Interval<Time> t_bounds,
                    State x_init)
            : _ode_id(ode_id),
              _t_bounds(move(t_bounds)), _x_init(move(x_init))
            {}

            Ode_id _ode_id;
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
