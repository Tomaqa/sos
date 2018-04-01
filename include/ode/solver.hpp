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
            using Ode_id = int;
            using Dt_id = int;
            using Dt_ids = vector<Dt_id>;
            using Param_keys = Expr::Eval<Real>::Param_keys;

            struct Context;
            struct Contexts;

            /// KONVENCE: 1. parametr je samotna funkce, posledni parametr je cas

            Solver() = default;
            // Solver(Odes_spec&& odes_spec_);
            // Solver(Ode_spec&& ode_spec_) : _odes_spec{ode_spec_} { }
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
            // rozlisit pripady kdy chci resit celou soustavu rovnic nebo jen dilci
                // - teoreticky mohou mit ruzne casove intervaly
            // virtual State solve(Context context_) const = 0;
            // State solve(const string& input) const;
            virtual Real solve_ode(Ode_id ode_id_, Context context_) const = 0;
            // Real solve_ode(Ode_id ode_id_, const string& input) const;
            virtual State solve_odes(Contexts contexts_) const = 0;
            // Real solve_odes(const string& input) const;
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
            // void eval_ode(Ode_id ode_id,
            //               State& dx, const State& x, Time t) const;
            // State eval_ode(Ode_id ode_id, const State& x, Time t) const
            //     { State dx; eval_ode(ode_id, dx, x, t); return move(dx); }
            void eval_odes_step(const Dt_ids& dt_ids_,
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

        struct Solver::Context {
            // Ode_id _ode_id;
            Dt_id _dt_id;
            Interval<Time> _t_bounds;
            State _x_init;
        };

        struct Solver::Contexts {
            Dt_ids _dt_ids;
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
