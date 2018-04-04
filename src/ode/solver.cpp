#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        Solver::Solver(Odes_spec odes_spec_, Param_keyss param_keyss_)
            : _odes_spec(move(odes_spec_))
        {
            const size_t n_odes = size();
            const size_t n_keyss = param_keyss_.size();
            const bool unified = n_keyss == 1 && n_odes > 1;
            if (unified) _is_unified.set();
            expect(unified || n_keyss == n_odes,
                   "Size of ODEs and set of non-unified "s
                   + "parameter keys mismatch: "
                   + to_string(n_odes) + " != " + to_string(n_keyss));
            for_each(param_keyss_, bind(&check_param_keys, _1));
            const size_t n_keys_front = param_keyss_.front().size();
            expect(!unified || (unified && n_keys_front >= n_odes),
                   "Size of unified parameter keys "s
                   +"must be at least equal to size of ODEs: "
                   + to_string(n_keys_front) + " < " + to_string(n_odes));

            odes_eval().reserve(size());
            if (unified) param_keyss_.resize(n_odes, param_keyss_.front());
            transform(odes_spec(),
                      std::make_move_iterator(std::begin(param_keyss_)),
                      std::back_inserter(odes_eval()),
                      bind(&create_ode_eval, _1, _2));
        }

        void Solver::add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_)
        {
            check_param_keys(param_keys_);
            odes_spec().emplace_back(move(ode_spec_));
            odes_eval().emplace_back(move(create_ode_eval(odes_spec().back(),
                                                          move(param_keys_))
                                         ));
            modified();
        }

        bool Solver::valid_keys(const Param_keys& param_keys_)
        {
            return param_keys_.size() >= 1;
        }

        void Solver::check_param_keys(const Param_keys& param_keys_)
        {
            expect(valid_keys(param_keys_),
                   "Invalid parameter keys: "s
                   + to_string(param_keys_));
        }

        Solver::Ode_eval Solver::create_ode_eval(Ode_spec& ode_spec_,
                                                 Param_keys param_keys_)
        {
            Ode_eval ode_eval_;
            ode_eval_.reserve(ode_spec_.size());
            transform(ode_spec_, std::back_inserter(ode_eval_),
                      [&param_keys_](Dt_spec& dspec){
                          return dspec.get_eval<Real>(param_keys_);
                      });
            return move(ode_eval_);
        }

        void Solver::modified() {
            _is_unified.invalidate();
            _has_param_t.invalidate();
        }

        bool Solver::is_unified(bool eval_if_unknown) const
        {
            if (_is_unified.is_valid()) return _is_unified.is_set();
            if (!eval_if_unknown) return false;
            const Param_keys& keys0 = cunif_param_keys_wo_check();
            const bool res =
                (all_of(codes_eval(),
                        [&keys0](const Ode_eval& oeval){
                            return code_param_keys(oeval) == keys0;
                        }));
            _is_unified.set(res);
            return res;
        }

        bool Solver::has_param_t(Ode_id ode_id_) const
        {
            if (_has_param_t.is_valid()) return _has_param_t.is_set();
            const bool res = ode_has_param_t(codes_eval()[ode_id_]);
            _has_param_t.set(res);
            return res;
        }

        bool Solver::ode_has_param_t(const Ode_eval& ode_eval_)
        {
            return dt_has_param_t(ode_eval_.front());
        }

        bool Solver::dt_has_param_t(const Dt_eval& dt_eval_)
        {
            return dt_eval_.cparam_keys().back() == "t";
        }

        Solver::Param_keyss Solver::cparam_keyss() const
        {
            Param_keyss param_keyss_;
            param_keyss_.reserve(size());
            transform(codes_eval(), std::back_inserter(param_keyss_),
                      bind(&Solver::code_param_keys, _1));
            return move(param_keyss_);
        }

        const Solver::Param_keys& Solver::cunif_param_keys() const
        {
            expect(is_unified(), "Parameter keys are not unified.");
            return cunif_param_keys_wo_check();
        }

        const Solver::Param_keys&
            Solver::code_param_keys(const Ode_eval& ode_eval_)
        {
            return ode_eval_.front().cparam_keys();
        }

        const Solver::Param_keys& Solver::cunif_param_keys_wo_check() const
        {
            return code_param_keys(codes_eval().front());
        }

        State Solver::solve_odes(Dt_ids dt_ids_, Contexts contexts_) const
        {
            const bool unified = is_unified() && equal(contexts_);
            return move(unified ? eval_unif_odes(move(dt_ids_),
                                                 move(contexts_.front()))
                                : eval_odes(move(dt_ids_), move(contexts_))
                       );
        }

        State Solver::solve_unif_odes(Dt_ids dt_ids_,
                                      Context context_) const
        {
            expect(is_unified(), "Attempt to solve unified ODEs,"s
                                 + " but parameter keys are not unified.");
            return move(eval_unif_odes(move(dt_ids_), move(context_)));
        }

        State Solver::eval_odes(Dt_ids&& dt_ids_, Contexts&& contexts_) const
        {
            State res;
            int size_ = size();
            res.reserve(size_);
            for (int i = 0; i < size_; i++) {
                res.emplace_back(solve_ode(dt_ids_[i],
                                           move(contexts_[i]),
                                           i));
            }
            return move(res);
        }

        // ! inefficient!!
        State Solver::eval_unif_odes(Dt_ids&& dt_ids_,
                                     Context&& context_) const
        {
            return move(eval_odes(move(dt_ids_), Contexts(size(), context_)));
        }

        void Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                    State& dx, const State& x, Time t) const
        {
            // ! do not construct in each step
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
            transform(codes_eval(), std::begin(dt_ids_), std::begin(dx), f);
        }

        State Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                          const State& x, Time t) const
        {
            State dx;
            eval_unif_odes_step(dt_ids_, dx, x, t);
            return move(dx);
        }

        void Solver::eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                                   Real& dx, const State& x, Time t) const
        {
            dx = eval_ode_step(ode_eval_, dt_id_, x, t);
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

        Real Solver::eval_dt_step(const Dt_eval& dt_eval_,
                                  Dt_eval_params params) const
        {
            return dt_eval_(move(params));
        }

        Solver::operator string () const
        {
            string str("");
            const Odes_spec& spec = codes_spec();
            const Odes_eval& eval = codes_eval();
            for (Ode_id oid = 0, size_ = size(); oid < size_; ++oid) {
                const Ode_spec& ospec = spec[oid];
                const Ode_eval& oeval = eval[oid];
                str += "ODE [" + to_string(oid) + "]\n";
                for (Dt_id did = 0, osize = ospec.size();
                     did < osize; ++did) {
                    const Dt_spec& dspec = ospec[did];
                    const Dt_eval& deval = oeval[did];
                    const Param_keys& deval_keys = deval.cparam_keys();
                    str += "  [" + to_string(did) + "]d"
                        + deval_keys[0] + "/dt = "
                        + to_string(dspec) + to_string(deval)
                        + (is_unified() ? "*" : "") + "\n";
                }
                str += "\n";
            }
            return move(str);
        }

        string to_string(const Solver& rhs)
        {
            return move((string)rhs);
        }

        ostream& operator <<(ostream& os, const Solver& rhs)
        {
            return (os << to_string(rhs));
        }

        Solver::Context::Context(Interval<Time> t_bounds_, State x_init_)
            : _t_bounds(move(t_bounds_)),
              _x_init(move(x_init_))
        {
            check_values();
        }

        Solver::Context::Context(const string& input)
        try {
            Expr expr(input);
            expect(expr.size() == 2, "Two top subexpressions expected.");
            expect(!expr[0]->is_token() && expr.cto_expr(0).size() == 2,
                   "Two tokens of time bounds expected.");
            const Expr& t_subexpr = expr.cto_expr(0);
            expect(t_subexpr.is_flat(),
                   "No further subexpressions expected.");
            expect(t_subexpr.cto_token(0).get_value_check<Real>(t_init())
                   && t_subexpr.cto_token(1).get_value_check<Real>(t_end()),
                   "Invalid values of time bounds.");

            expect(!expr[1]->is_token(),
                   "Initial values must be enclosed in subexpression.");
            const Expr& x_subexpr = expr.cto_expr(1);
            expect(x_subexpr.is_flat(),
                   "No further subexpressions expected.");
            x_init() = move(x_subexpr.flat_transform<Real>());

            check_values();
        }
        catch (const Error& e) {
            throw "Invalid format of input context '"s + input + "':\n" + e;
        }

        void Solver::Context::check_values() const
        {
            expect(ct_init() <= ct_end(),
                   "Invalid time interval: "s
                   + std::to_string(ct_init()) + ", "
                   + std::to_string(ct_end()));
        }

        Solver::Context::operator string () const
        {
            return "( "s + to_string(ct_bounds()) + " )"
                          + " ( " + to_string(cx_init()) + ")";
        }

        string to_string(const Solver::Context& rhs)
        {
            return move((string)rhs);
        }

        ostream& operator <<(ostream& os, const Solver::Context& rhs)
        {
            return (os << to_string(rhs));
        }

        bool operator ==(const Solver::Context& lhs,
                         const Solver::Context& rhs)
        {
            return lhs.ct_bounds() == rhs.ct_bounds()
                && lhs.cx_init() == rhs.cx_init();
        }
    }
}
