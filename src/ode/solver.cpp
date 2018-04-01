#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        Solver::Solver(Odes_spec odes_spec_)
            : _odes_spec(move(odes_spec_)),
              _odes_eval(size())
        {
            std::transform(std::begin(_odes_spec), std::end(_odes_spec),
                           std::begin(_odes_eval),
                           bind(&Solver::create_ode_eval, this, _1));
        }

        void Solver::add_ode_spec(Ode_spec ode_spec_)
        {
            _odes_spec.emplace_back(move(ode_spec_));
            _odes_eval.emplace_back(create_ode_eval(_odes_spec.back()));
        }

        Solver::Ode_eval Solver::create_ode_eval(Ode_spec& ode_spec_)
        {
            Ode_eval ode_eval_(ode_spec_.size());
            std::transform(std::begin(ode_spec_), std::end(ode_spec_),
                           std::begin(ode_eval_),
                               //! param_keys
                           bind(&Dt_spec::get_eval<Real>, _1, Param_keys{}));
            return move(ode_eval_);
        }

        // !! ruzne ODE musi mit jednotne parametry!
        void Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                    State& dx, const State& x, Time t) const
        {
            // ! neptat se v kazdem kroku
            function<Real(const Ode_eval& ode_eval_, Dt_id dt_id_)> f;
            if (has_param_t()) {
                f = [this, &x, t](const Ode_eval& ode_eval_, Dt_id dt_id_){
                    return eval_dt_step(ode_eval_[dt_id_], x, t);
                };
            }
            else {
                f = [this, &x](const Ode_eval& ode_eval_, Dt_id dt_id_){
                    return eval_dt_step(ode_eval_[dt_id_], x);
                };
            }
            std::transform(std::begin(codes_eval()), std::end(codes_eval()),
                           std::begin(dt_ids_),
                           std::begin(dx),
                           f);
        }

        State Solver::solve_odes(Contexts contexts_) const
        {
            State x;
            int size_ = size();
            x.reserve(size_);
            for (int i = 0; i < size_; i++) {
                x.emplace_back(solve_ode(Context{contexts_._dt_ids[i],
                                                 contexts_._t_bounds,
                                                 contexts_._x_init,
                                                }, i));
            }
            return move(x);
        }

        void Solver::eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                                   Real& dx, const State& x, Time t) const
        {
            dx = has_param_t(ode_eval_)
                ? eval_dt_step(ode_eval_[dt_id_], x, t)
                : eval_dt_step(ode_eval_[dt_id_], x);
        }

        Real Solver::eval_dt_step(const Dt_eval& dt_eval_,
                                  const State& x, Time t) const
        {
            Dt_eval_params params(x);
            params.emplace_back(t);
            return eval_dt_step(dt_eval_, move(params));
        }

        Solver::Context::Context(const string& input)
        {
            if (!regex_match(input, input_re)) {
                throw Error("Invalid format of input context: " + input);
            }
            Expr expr(input);

            // ! redundantni, jen pro zacatek
            assert((expr.size() == input_expr_size));
            assert((expr[0]->is_token()));
            assert((!expr[1]->is_token() && expr.cto_expr(1).size() == 2));
            assert((!expr[2]->is_token()));

            const Expr_token& id_token = expr.cto_token(0);
            assert((id_token.is_value<Dt_id>()));
            id_token.get_value_check<Dt_id>(_dt_id);

            const Expr& t_subexpr = expr.cto_expr(1);
            assert((t_subexpr.is_flat()));
            _t_bounds = make_pair(t_subexpr.cto_token(0).get_value<Real>(),
                                  t_subexpr.cto_token(1).get_value<Real>());

            const Expr& x_subexpr = expr.cto_expr(2);
            assert((x_subexpr.is_flat()));
            _x_init = move(x_subexpr.flat_transform<Real>());
        }

        ostream& operator <<(ostream& os, const Solver::Context& rhs)
        {
            os << rhs._dt_id
               << " ( " << rhs._t_bounds.first << rhs._t_bounds.second << " )"
               << " (";
            for (auto x : rhs._x_init) os << " " << x;
            os << " )";
            return os;
        }

        bool operator ==(const Solver::Context& lhs, const Solver::Context& rhs)
        {
            return lhs._dt_id == rhs._dt_id
                && lhs._t_bounds == rhs._t_bounds
                && lhs._x_init == rhs._x_init;
        }
    }
}
