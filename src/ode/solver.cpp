#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        Solver::Solver(Odes_spec odes_spec_, Param_keyss param_keyss_)
            : _odes_spec(move(odes_spec_))
        {
            const size_t n_odes = size();
            const size_t n_keyss = param_keyss_.size();
            const bool unif_keys = n_keyss == 1 && n_odes > 1;
            expect(unif_keys || n_keyss == n_odes,
                   "Size of ODEs and set of non-uniformed "s
                   + "parameter keys mismatch: "
                   + to_string(n_odes) + " != " + to_string(n_keyss));
            for_each(std::begin(param_keyss_), std::end(param_keyss_),
                     bind(&check_keys, _1));
            const size_t n_keys_front = param_keyss_.front().size();
            expect(!unif_keys
                   || (unif_keys && n_keys_front >= n_odes),
                   "Size of uniformed parameter keys "s
                   +"must be at least equal to size of ODEs: "
                   + to_string(n_keys_front) + " < " + to_string(n_odes));

            odes_eval().reserve(size());
            if (unif_keys) param_keyss_.resize(n_odes, param_keyss_.front());
            std::transform(std::begin(odes_spec()), std::end(odes_spec()),
                           std::make_move_iterator(std::begin(param_keyss_)),
                           std::back_inserter(odes_eval()),
                           bind(&create_ode_eval, _1, _2));
        }

        void Solver::add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_)
        {
            check_keys(param_keys_);
            odes_spec().emplace_back(move(ode_spec_));
            odes_eval().emplace_back(move(create_ode_eval(odes_spec().back(),
                                                          move(param_keys_))
                                         ));
            modified();
        }

        Solver::Ode_eval Solver::create_ode_eval(Ode_spec& ode_spec_,
                                                 Param_keys param_keys_)
        {
            Ode_eval ode_eval_(ode_spec_.size());
            std::transform(std::begin(ode_spec_), std::end(ode_spec_),
                           std::begin(ode_eval_),
                           bind(&Dt_spec::get_eval<Real>,
                                _1, param_keys_));
            return move(ode_eval_);
        }

        void Solver::modified() {
            _has_param_t = false;
        }

        bool Solver::has_param_t(Ode_id ode_id_) const
        {
            if (_has_param_t) return true;
            if (ode_has_param_t(codes_eval()[ode_id_])) _has_param_t = true;
            return _has_param_t;
        }

        State Solver::solve_odes(Dt_ids dt_ids_, Contexts contexts_) const
        {
            State res;
            int size_ = size();
            res.reserve(size_);
            for (int i = 0; i < size_; i++) {
                res.emplace_back(solve_ode(dt_ids_[i], move(contexts_[i]), i));
            }
            return move(res);
        }

        State Solver::solve_unif_odes(Dt_ids dt_ids_,
                                      Context context_) const
        {
            return move(solve_odes(move(dt_ids_), Contexts(size(), context_)));
        }

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

        Real Solver::eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                                   const State& x, Time t) const
        {
            return ode_has_param_t(ode_eval_)
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
            const string& err_msg("Invalid format of input context: "s + input);
            expect(regex_match(input, input_re), err_msg);
            Expr expr(input);
            expect(expr.size() == input_expr_size, err_msg);

            // ! redundantni, jen pro zacatek
            assert((!expr[0]->is_token() && expr.cto_expr(0).size() == 2));
            assert((!expr[1]->is_token()));

            const Expr& t_subexpr = expr.cto_expr(0);
            assert((t_subexpr.is_flat()));
            _t_bounds = make_pair(t_subexpr.cto_token(0).get_value<Real>(),
                                  t_subexpr.cto_token(1).get_value<Real>());

            const Expr& x_subexpr = expr.cto_expr(1);
            assert((x_subexpr.is_flat()));
            _x_init = move(x_subexpr.flat_transform<Real>());

            check_values();
        }

        void Solver::Context::check_values() const
        {
            expect(_t_bounds.first <= _t_bounds.second,
                   "Invalid time interval: "s
                   + to_string(_t_bounds.first) + ", "
                   + to_string(_t_bounds.second));
        }

        Solver::Context::operator string () const
        {
            return string("( "s + to_string(t_bounds().first)
                          + to_string(t_bounds().second) + " ) ("
                          + to_string(x_init()) + " )");
        }

        bool operator ==(const Solver::Context& lhs, const Solver::Context& rhs)
        {
            return lhs._t_bounds == rhs._t_bounds
                && lhs._x_init == rhs._x_init;
        }

        const regex Solver::Context::input_re{
            "\\s*\\(?\\s*"s
            + "\\((\\s*" + Expr::re_float + "\\s*){2}\\)\\s*"
            + "\\((\\s*" + Expr::re_float + "\\s*)*\\)\\s*"
            + "\\)?\\s*"
        };
    }
}
