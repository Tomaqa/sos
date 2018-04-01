#ifndef ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
#define ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430

#include "ode.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

#include <regex>

namespace SOS {
    namespace ODE {
        class Solver {
        public:
            using Dt_spec = Expr;
            using Ode_spec = vector<Dt_spec>;
            using Odes_spec = vector<Ode_spec>;
            using Ode_id = int;
            using Dt_id = int;
            using Dt_ids = vector<Dt_id>;
            using Param_keys = Expr::Eval<Real>::Param_keys;

            class Context;
            struct Contexts;

            /// KONVENCE: 1. parametr je samotna funkce, posledni parametr je cas

            Solver() = default;
            Solver(Odes_spec odes_spec_);
            Solver(Ode_spec ode_spec_) : Solver(Odes_spec{move(ode_spec_)}) { }
            virtual ~Solver() = default;
            Solver(const Solver& rhs) = delete;
            Solver& operator =(const Solver& rhs) = delete;
            Solver(Solver&& rhs) = default;
            Solver& operator =(Solver&& rhs) = default;

            size_t size() const noexcept { return _odes_spec.size(); }
            Time step_size() const noexcept { return _step_size; }
            void set_step_size(Time step_size_) noexcept
                { _step_size = step_size_; }
            void add_ode_spec(Ode_spec ode_spec_);
            virtual Real solve_ode(Context context_, Ode_id ode_id_ = 0) const = 0;
            //
            State solve_odes(Contexts contexts_) const;
            virtual State solve_unif_odes(Contexts contexts_) const = 0;
        protected:
            using Dt_eval = Expr::Eval<Real>;
            using Ode_eval = vector<Dt_eval>;
            using Odes_eval = vector<Ode_eval>;

            const Odes_spec& codes_spec() const
                { return _odes_spec; }
            const Odes_eval& codes_eval() const
                { return _odes_eval; }
            Odes_spec& codes_spec()
                { return _odes_spec; }
            Odes_eval& odes_eval()
                { return _odes_eval; }

            Ode_eval create_ode_eval(Ode_spec& ode_spec_);
            void eval_unif_odes_step(const Dt_ids& dt_ids_,
                                     State& dx, const State& x, Time t) const;
            void eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                               Real& dx, const State& x, Time t) const;
        private:
            using Dt_eval_params = Dt_eval::Param_values;

            bool has_param_t(const Dt_eval& dt_eval_) const
                { return dt_eval_.cparam_keys().back() == "t"; }
            bool has_param_t(const Ode_eval& ode_eval_) const
                { return has_param_t(ode_eval_[0]); }
            bool has_param_t() const
                { return has_param_t(_odes_eval[0]); }
            Real eval_dt_step(const Dt_eval& dt_eval_,
                              const State& x, Time t) const;
            Real eval_dt_step(const Dt_eval& dt_eval_,
                              Dt_eval_params params) const
                { return dt_eval_(move(params)); }

            Time _step_size{1.0};
            Odes_spec _odes_spec;
            Odes_eval _odes_eval;
        };

        class Solver::Context {
        public:
            Context(const string& input);

            Dt_id _dt_id;
            Interval<Time> _t_bounds;
            State _x_init;
        protected:
            const regex input_re{
                "\\s*\\d+\\s*"s
                + "\\((\\s*" + Expr::re_float + "){2}\\) *"
                + "\\((\\s*" + Expr::re_float + ")+\\)\\s*"
            };
            static constexpr size_t input_expr_size = 3;
        };

        struct Solver::Contexts {
            Dt_ids _dt_ids;
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
