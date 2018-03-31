#ifndef ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
#define ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430

#include "ode.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

namespace SOS {
    namespace ODE {
        class Solver {
        public:
            using Dt_spec = Expr;
            using Ode_spec = vector<Dt_spec>;
            using Odes_spec = vector<Ode_spec>;
            using Dt_id = int;
            using Ode_id = int;

            struct Context;

            Solver(Odes_spec&& odes_spec_);
            Solver(Ode_spec&& ode_spec_) : _odes_spec{ode_spec_} { }
            virtual ~Solver() = default;
            Solver(const Solver& rhs) = delete;
            Solver& operator =(const Solver& rhs) = delete;
            Solver(Solver&& rhs) = default;
            Solver& operator =(Solver&& rhs) = default;

            size_t size() const noexcept { return _odes_spec.size(); }
            Time step_size() const noexcept { return _step_size; }
            void set_step_size(Time step_size_) noexcept
                { _step_size = step_size_; }
            virtual State solve(Context context_) const = 0;
            State solve(const string& input) const;
        protected:
            using Dt_eval = Expr::Eval<Real>;
            using Ode_eval = vector<Dt_eval>;
            using Odes_eval = vector<Ode_eval>;

            using Dt_params = Dt_eval::Param_values;

            void eval_ode(Ode_id ode_id,
                          State& dx, const State& x, Time t) const;
            State eval_ode(Ode_id ode_id, const State& x, Time t) const
                { State dx; eval_ode(ode_id, dx, x, t); return move(dx); }
        private:
            const Ode_spec& code_spec(Ode_id ode_id) const
                { return _odes_spec[ode_id]; }
            const Ode_eval& code_eval(Ode_id ode_id) const
                { return _odes_eval[ode_id]; }
            Ode_eval& ode_eval(Ode_id ode_id)
                { return _odes_eval[ode_id]; }
            Real eval_dt(const Dt_eval& dt_eval_, const State& x, Time t) const;

            Time _step_size{1.0};
            Odes_spec _odes_spec;
            Odes_eval _odes_eval;
        };

        struct Solver::Context {
            // Context(Ode_id ode_id,
            //         Interval<Time> t_bounds,
            //         State x_init)
            //     : _ode_id(ode_id),
            //       _t_bounds(move(t_bounds)), _x_init(move(x_init))
            // {}

            Ode_id _ode_id;
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
