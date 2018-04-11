#include "ode/solver.hpp"
#include "ode/solver/context.hpp"

namespace SOS {
    namespace ODE {
        Solver::Solver(Odes_spec odes_spec_, Param_keyss param_keyss_)
            : _odes_spec(move(odes_spec_)),
              _state_fs(size())
        {
            check_empty(param_keyss_);
            for_each(codes_spec(), bind(&Solver::check_ode_spec, _1));
            set_odes_eval(move(param_keyss_));
        }

        Solver::Solver(Odes_spec odes_spec_, Param_keys param_keys_)
            : Solver(move(odes_spec_), Param_keyss{move(param_keys_)})
        { }

        Solver::Solver(Ode_spec ode_spec_, Param_keys param_keys_)
            : Solver(Odes_spec{move(ode_spec_)},
                     Param_keyss{move(param_keys_)})
        { }

        Solver::Solver(Spec spec)
            : Solver(move(spec.first), move(spec.second))
        { }

        Solver::Solver(const string& input)
        try
            : Solver(Expr(input))
        { }
        catch (const Error& err) {
            throw "Invalid format of input ODEs specification\n'"s
                  + input + "'\n: " + err;
        }

        Solver::Solver(const Expr& expr)
        try {
            expect(expr.size() == 2 && expr.is_deep(),
                   "Expected two expressions of ODEs specifications "s
                   + "and set of parameter keys "
                   + "at the top level.");
            parse_odes_spec(expr.cto_expr(0));
            Param_keyss param_keyss_(move(
                parse_param_keyss(expr.cto_expr(1))
            ));
            check_empty(param_keyss_);
            set_odes_eval(move(param_keyss_));
            _state_fs.resize(size());
        }
        catch (const Error& err) {
            throw "Invalid format of input ODEs specification\n'"s
                  + to_string(expr) + "'\n: " + err;
        }

        void Solver::set_odes_eval(Param_keyss&& param_keyss_)
        {
            const bool unified = check_param_keyss(param_keyss_);
            odes_eval().reserve(size());
            if (!unified) {
                add_odes_eval(move(param_keyss_));
            }
            else {
                add_unif_odes_eval(move(param_keyss_.front()));
            }
        }

        void Solver::parse_odes_spec(const Expr& expr)
        {
            expect(expr.is_deep(),
                   "Expected expressions "s
                   + "with ODE specifications.");
            _odes_spec.reserve(expr.size());
            for (auto& eptr : expr) {
                const Expr& espec = Expr::cptr_to_expr(eptr);
                Ode_spec ospec(move(espec.transform_to_exprs()));
                check_ode_spec(ospec);
                _odes_spec.emplace_back(move(ospec));
            }
        }

        Solver::Param_keyss Solver::parse_param_keyss(const Expr& expr)
        {
            if (!expr.is_deep()) {
                return Param_keyss{move(parse_param_keys(expr))};
            }
            Param_keyss param_keyss_;
            param_keyss_.reserve(expr.size());
            transform(expr.transform_to_exprs(),
                      std::back_inserter(param_keyss_),
                      bind(&Solver::parse_param_keys, _1));
            return move(param_keyss_);
        }

        Solver::Param_keys Solver::parse_param_keys(const Expr& expr)
        {
            return move(expr.transform_to_tokens());
        }

        void Solver::check_empty(const Param_keyss& param_keyss_) const
        {
            if (empty()) {
                expect(param_keyss_.empty(),
                       "No ODE given and parameter keys are non-empty.");
            }
        }

        void Solver::check_ode_spec(const Ode_spec& ode_spec_)
        {
            expect(valid_ode_spec(ode_spec_),
                   "Empty ODE specification detected.");
        }

        bool Solver::valid_ode_spec(const Ode_spec& ode_spec_)
        {
            return !ode_spec_.empty();
        }

        bool Solver::check_param_keyss(const Param_keyss& param_keyss_) const
        {
            const size_t n_odes = size();
            const size_t n_keyss = param_keyss_.size();
            const bool unified = n_keyss == 1 && n_odes > 1;
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
            return unified;
        }

        void Solver::check_param_keys(const Param_keys& param_keys_)
        {
            expect(valid_keys(param_keys_),
                   "Invalid parameter keys: "s
                   + to_string(param_keys_));
        }

        bool Solver::valid_keys(const Param_keys& param_keys_)
        {
            int size_ = param_keys_.size();
            const auto eit = std::end(param_keys_);
            auto pos = std::find(std::begin(param_keys_), eit, "t");
            if (pos != eit) {
                if (pos != eit-1) return false;
                --size_;
            }
            return size_ > 0;
        }

        void Solver::check_dt_ids(const Dt_ids& dt_ids_) const
        {
            expect(dt_ids_.size() == size(),
                   "Expected dt index for every ODEs ("s
                   + to_string(size()) + "), got: "
                   + to_string(dt_ids_.size()));
        }

        Solver::Param_keys_ptr
            Solver::new_param_keys(Solver::Param_keys&& param_keys_)
        {
            return Dt_eval::new_param_keys(move(param_keys_));
        }

        void Solver::add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_)
        {
            check_ode_spec(ode_spec_);
            check_param_keys(param_keys_);
            odes_spec().emplace_back(move(ode_spec_));
            add_ode_eval(odes_spec().back(), move(param_keys_));
            modified();
        }

        void Solver::add_odes_eval(Param_keyss&& param_keyss_)
        {
            transform(odes_spec(),
                      std::make_move_iterator(std::begin(param_keyss_)),
                      std::back_inserter(odes_eval()),
                      [](Ode_spec& ospec, const Param_keys& keys_){
                          return create_ode_eval(ospec, keys_);
                      });
        }

        void Solver::add_unif_odes_eval(Param_keys&& param_keys_)
        {
            Param_keys_ptr param_keys_ptr_ =
                new_param_keys(move(param_keys_));
            transform(odes_spec(),
                      std::back_inserter(odes_eval()),
                      [&param_keys_ptr_](Ode_spec& ospec){
                          return create_ode_eval(ospec, param_keys_ptr_);
                      });
            _is_unified.set();
        }

        template <typename Keys>
        void Solver::add_ode_eval(Ode_spec& ode_spec_, Keys&& keys_)
        {
            odes_eval().emplace_back(
                move(create_ode_eval(ode_spec_, forward<Keys>(keys_)))
            );
        }

        Solver::Ode_eval
            Solver::create_ode_eval(Ode_spec& ode_spec_,
                                    Param_keys param_keys_)
        {
            Param_keys_ptr param_keys_ptr_ =
                new_param_keys(move(param_keys_));
            return move(create_ode_eval(ode_spec_, move(param_keys_ptr_)));
        }

        Solver::Ode_eval
            Solver::create_ode_eval(Ode_spec& ode_spec_,
                                    Param_keys_ptr param_keys_ptr_)
        {
            Ode_eval ode_eval_;
            ode_eval_.reserve(ode_spec_.size());
            transform(ode_spec_, std::back_inserter(ode_eval_),
                      [&param_keys_ptr_](Dt_spec& dspec){
                          return dspec.get_eval<Real>(param_keys_ptr_);
                      });
            return move(ode_eval_);
        }

        void Solver::modified() {
            _is_unified.invalidate();
            _has_param_t.invalidate();
        }

        bool Solver::is_unified() const
        {
            if (empty()) return false;
            if (_is_unified.is_valid()) return _is_unified.is_set();
            const Param_keys& keys0 = cunif_param_keys_wo_check();
            const bool res =
                (all_of(codes_eval(),
                        [&keys0](const Ode_eval& oeval){
                            return code_param_keys(oeval) == keys0;
                        }));
            _is_unified.set(res);
            return res;
        }

        bool Solver::has_unif_param_t() const
        {
            if (empty() || !is_unified()) return false;
            if (_has_param_t.is_valid()) return _has_param_t.is_set();
            const bool res = ode_has_param_t(def_ode_id);
            _has_param_t.set(res);
            return res;
        }

        bool Solver::ode_has_param_t(Ode_id ode_id_) const
        {
            return ode_has_param_t(code_eval(ode_id_));
        }

        bool Solver::ode_has_param_t(const Ode_eval& ode_eval_)
        {
            return dt_has_param_t(ode_eval_.front());
        }

        bool Solver::dt_has_param_t(const Dt_eval& dt_eval_)
        {
            return to_string(dt_eval_.cparam_keys().back()) == "t";
        }

        Solver::Param_keyss Solver::cparam_keyss() const
        {
            if (empty()) return {};
            Param_keyss param_keyss_;
            param_keyss_.reserve(size());
            transform(codes_eval(), std::back_inserter(param_keyss_),
                      [](const Ode_eval& oeval){
                          return code_param_keys(oeval);
                      });
            return move(param_keyss_);
        }

        const Solver::Param_keys& Solver::cunif_param_keys() const
        {
            expect(is_unified(), "Parameter keys are not unified.");
            return cunif_param_keys_wo_check();
        }

        const Solver::Param_keys&
            Solver::code_param_keys(Ode_id ode_id_) const
        {
            return code_param_keys(code_eval(ode_id_));
        }

        const Solver::Param_keys&
            Solver::code_param_keys(const Ode_eval& ode_eval_)
        {
            return ode_eval_.front().cparam_keys();
        }

        const Solver::Param_keys& Solver::cunif_param_keys_wo_check() const
        {
            return code_param_keys(code_eval());
        }

        const Solver::Param_key&
            Solver::code_param_key(Ode_id ode_id_, bool unified) const
        {
            return code_param_keys(ode_id_)[unified ? ode_id_
                                                    : def_ode_id];
        }

        Real Solver::solve_ode(Dt_id dt_id_, Context context_,
                               Ode_id ode_id_) const
        {
            add_param_t(ode_has_param_t(ode_id_), context_, ode_id_);
            return eval_ode(ode_id_, dt_id_, move(context_));
        }

        State Solver::solve_odes(Dt_ids dt_ids_, Contexts contexts_) const
        {
            check_dt_ids(dt_ids_);
            const bool unified = is_unified()
                                 && (contexts_.size() == 1
                                     || all_equal(contexts_));
            if (unified) {
                return move(
                    solve_unif_odes_wo_check(move(dt_ids_),
                                             move(contexts_.front()))
                );
            }
            for_each(contexts_, std::begin(codes_eval()),
                    [this](Context& ctx, const Ode_eval& oeval){
                        const bool has_t = ode_has_param_t(oeval);
                        add_param_t(has_t, ctx, code_eval_id(oeval));
                    });
            return move(eval_odes(move(dt_ids_), move(contexts_)));
        }

        State Solver::solve_unif_odes(Dt_ids dt_ids_,
                                      Context context_) const
        {
            expect(is_unified(), "Attempt to solve unified ODEs,"s
                                 + " but parameter keys are not unified.");
            check_dt_ids(dt_ids_);
            return move(solve_unif_odes_wo_check(move(dt_ids_),
                                                 move(context_)));
        }

        State Solver::solve_unif_odes_wo_check(Dt_ids dt_ids_,
                                               Context context_) const
        {
            add_param_t(has_unif_param_t(), context_);
            return move(eval_unif_odes(move(dt_ids_), move(context_)));
        }

        State Solver::solve(const string& input) const
        {
            return move(solve(Expr(input)));
        }

        State Solver::solve(const Expr& expr) const
        {
            expect(expr.size() == 2 && expr.is_deep(),
                   "Expected two expressions of chosen dt variants "s
                   + "and context(s) for ODEs.");

            Dt_ids dt_ids_(expr.cto_expr(0).transform_to_args<Dt_id>());

            Expr ctx_expr(expr.cto_expr(1));
            expect(ctx_expr.is_deep(),
                   "Expected subexpressions with context(s) for ODEs.");
            if (ctx_expr.size() == 1) {
                return move(solve_unif_odes(move(dt_ids_),
                                            Context(ctx_expr.cto_expr(0))
                           ));
            }
            Contexts contexts_;
            contexts_.reserve(ctx_expr.size());
            transform(ctx_expr.transform_to_exprs(),
                      std::back_inserter(contexts_),
                      [](const Expr& e){ return Context(e); });
            return solve_odes(move(dt_ids_), move(contexts_));
        }

        Solver::State_f& Solver::state_f(Ode_id ode_id_) const
        {
            return state_fs()[ode_id_];
        }

        void Solver::set_state_f(bool has_t, Ode_id ode_id_) const
        {
            state_f(ode_id_) = get_state_f(has_t);
        }

        Solver::State_f Solver::get_state_f(bool has_t)
        {
            if (!has_t) {
                return [](const State& x, Time) -> const State& {
                    return x;
                };
            }
            return [](const State& x, Time t) -> const State& {
                const_cast<Real&>(x.back()) = t;
                return x;
            };
        }

        const State& Solver::state(const State& x, Time t,
                                   Ode_id ode_id_) const
        {
            return state_f(ode_id_)(x, t);
        }

        void Solver::context_add_param_t(bool has_t, Context& context_)
        {
            if (has_t) context_.add_param_t();
        }

        void Solver::add_param_t(bool has_t, Context& context_,
                                 Ode_id ode_id_) const
        {
            set_state_f(has_t, ode_id_);
            context_add_param_t(has_t, context_);
        }

        State Solver::eval_odes(Dt_ids&& dt_ids_, Contexts&& contexts_) const
        {
            State res;
            const int size_ = size();
            res.reserve(size_);
            for (int i = 0; i < size_; i++) {
                res.emplace_back(eval_ode(i, dt_ids_[i],
                                          move(contexts_[i])));
            }
            return move(res);
        }

        template <typename OutputIt>
        void Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                         OutputIt dx_it,
                                         const State& x, Time t) const
        {
            transform(codes_eval(), std::begin(dt_ids_),
                      move(dx_it),
                      [this, &x, t](const Ode_eval& oeval, Dt_id dt_id_){
                          return eval_unif_ode_step(code_eval_id(oeval),
                                                    dt_id_, x, t);
                      });
        }

        template
        void Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                         State::iterator dx_it,
                                         const State& x, Time t) const;

        // ! inefficient!
        State Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                          const State& x, Time t) const
        {
            State dx;
            const size_t state_size = x.size();
            dx.reserve(state_size);
            eval_unif_odes_step(dt_ids_, std::back_inserter(dx), x, t);
            if (state_size > size()) dx.emplace_back(Real());
            return move(dx);
        }

        void Solver::eval_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                   Real& dx, const State& x, Time t) const
        {
            dx = eval_ode_step(ode_id_, dt_id_, x, t);
        }

        Real Solver::eval_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                   const State& x, Time t) const
        {
            return eval_dt_step(cdt_eval(ode_id_, dt_id_), ode_id_, x, t);
        }

        void Solver::eval_unif_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                        Real& dx, const State& x, Time t)
                                        const
        {
            dx = eval_unif_ode_step(ode_id_, dt_id_, x, t);
        }

        Real Solver::eval_unif_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                        const State& x, Time t) const
        {
            return eval_dt_step(cdt_eval(ode_id_, dt_id_), def_ode_id, x, t);
        }

        Real Solver::eval_dt_step(const Dt_eval& dt_eval_, Ode_id state_id,
                                  const State& x, Time t) const
        {
            return dt_eval_(state(x, t, state_id));
        }

        Solver::operator string () const
        {
            string str("");
            const bool unified = is_unified();
            const Odes_spec& spec = codes_spec();
            const Odes_eval& eval = codes_eval();
            for (Ode_id oid = 0, size_ = size(); oid < size_; ++oid) {
                const Ode_spec& ospec = spec[oid];
                const Ode_eval& oeval = eval[oid];
                const bool has_t = ode_has_param_t(oid);
                str += "ODE [" + to_string(oid) + "]\n";
                for (Dt_id did = 0, osize = ospec.size();
                     did < osize; ++did) {
                    const Dt_spec& dspec = ospec[did];
                    const Dt_eval& deval = oeval[did];
                    const Param_key& pkey = code_param_key(oid, unified);
                    str += "  [" + to_string(did) + "]d"
                        + to_string(pkey) + "/dt = "
                        + to_string(dspec) + to_string(deval)
                        + (unified ? "*" : "")
                        + (has_t ? "%" : "")
                        + "\n";
                }
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
    }
}
