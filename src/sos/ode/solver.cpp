#include "ode/solver.hpp"

#include <set>

namespace SOS {
    using std::set;

    namespace ODE {
        Solver::Solver(Odes_spec odes_spec_, Param_keyss param_keyss_,
                       bool unify)
            : _odes_spec(move(odes_spec_)),
              _state_fs(size()),
              _trajects(size())
        {
            for_each(codes_spec(), bind(&Solver::check_ode_spec, _1));
            set_odes_eval(move(param_keyss_), unify);
        }

        Solver::Solver(Odes_spec odes_spec_, Param_keys param_keys_)
            : Solver(move(odes_spec_), Param_keyss{move(param_keys_)})
        { }

        Solver::Solver(Ode_spec ode_spec_, Param_keys param_keys_)
            : Solver(Odes_spec{move(ode_spec_)},
                     Param_keyss{move(param_keys_)})
        { }

        Solver::Solver(Spec spec, bool unify)
            : Solver(move(spec.first), move(spec.second), unify)
        { }

        Solver::Solver(string input, bool unify)
            : Solver(istringstream(move(input)), unify)
        { }

        Solver::Solver(istream& is, bool unify)
        try : Solver(Expr(is), unify)
        { }
        catch (const Error& err) {
            throw "Invalid format of input ODEs specification:\n" + err;
        }

        Solver::Solver(istream&& is, bool unify)
            : Solver(is, unify)
        { }

        Solver::Solver(Expr expr, bool unify)
        try {
            bool parse_unify = (
                 expr.size() == 3
                 && !expr.get()->is_etoken()
                 && expr.cpeek()->is_etoken() && expr.get_token() == "*"
                 && !expr.get()->is_etoken()
            );
            expr.reset_pos();
            unify |= parse_unify;
            expect(parse_unify || (expr.size() == 2 && expr.is_deep()),
                   "Expected two expressions of ODEs specifications "s
                   + "and set of parameter keys "
                   + "at top level "
                   + "with optional '*' token in between "
                   + "(to unify parameter keys).");
            parse_odes_spec(expr.get_expr());
            if (parse_unify) expr.next();
            Param_keyss param_keyss_ = parse_param_keyss(expr.get_expr());
            check_empty(param_keyss_);
            set_odes_eval(move(param_keyss_), unify);
        }
        catch (const Error& err) {
            throw "Invalid format of input ODEs specification\n'"s
                  + to_string(expr) + "'\n: " + err;
        }

        void Solver::set_odes_eval(Param_keyss param_keyss_, bool unify)
        {
            check_empty(param_keyss_);
            bool unified = check_param_keyss(param_keyss_);
            if (!unified && unify) {
                param_keyss_ =
                    Param_keyss{move(unify_param_keys(move(param_keyss_)))};
                unified = true;
            }
            odes_eval().reserve(size());
            if (unified) {
                Param_keys param_keys_ = move(param_keyss_.front());
                add_unif_odes_eval(param_keys_);
                state_fs().resize(1);
                init_unif_traject(move(param_keys_));
            }
            else {
                add_odes_eval(param_keyss_);
                state_fs().resize(size());
                init_trajects(move(param_keyss_));
            }
        }

        void Solver::parse_odes_spec(Expr& expr)
        {
            expect(expr.is_deep(),
                   "Expected expressions "s
                   + "with ODE specifications.");
            _odes_spec.reserve(expr.size());
            for (auto& eptr : expr) {
                Expr& espec = Expr::ptr_to_expr(eptr);
                Ode_spec ospec = espec.transform_to_exprs();
                check_ode_spec(ospec);
                _odes_spec.emplace_back(move(ospec));
            }
        }

        Param_keyss Solver::parse_param_keyss(Expr& expr)
        {
            if (!expr.is_deep()) {
                return Param_keyss{parse_param_keys(move(expr))};
            }
            Param_keyss param_keyss_;
            param_keyss_.reserve(expr.size());
            transform(expr.transform_to_exprs(),
                      std::back_inserter(param_keyss_),
                      bind(&Solver::parse_param_keys, _1));
            return param_keyss_;
        }

        Param_keys Solver::parse_param_keys(Expr&& expr)
        {
            return expr.transform_to_tokens();
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
            const bool unified = n_keyss == 1 && n_odes >= 1;
            expect(unified || n_keyss == n_odes,
                   "Size of ODEs and set of independent "s
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
            Solver::new_param_keys(Param_keys&& param_keys_)
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

        void Solver::add_odes_eval(Param_keyss param_keyss_)
        {
            transform(odes_spec(),
                      std::make_move_iterator(std::begin(param_keyss_)),
                      std::back_inserter(odes_eval()),
                      [](Ode_spec& ospec, Param_keys&& keys_){
                          return create_ode_eval(ospec, move(keys_));
                      });
        }

        void Solver::add_unif_odes_eval(Param_keys param_keys_)
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
                create_ode_eval(ode_spec_, forward<Keys>(keys_))
            );
        }

        Solver::Ode_eval
            Solver::create_ode_eval(Ode_spec& ode_spec_,
                                    Param_keys param_keys_)
        {
            Param_keys_ptr param_keys_ptr_ =
                new_param_keys(move(param_keys_));
            return create_ode_eval(ode_spec_, move(param_keys_ptr_));
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
            return ode_eval_;
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

        Param_keyss Solver::cparam_keyss() const
        {
            if (empty()) return {};
            Param_keyss param_keyss_;
            param_keyss_.reserve(size());
            transform(codes_eval(), std::back_inserter(param_keyss_),
                      [](const Ode_eval& oeval){
                          return code_param_keys(oeval);
                      });
            return param_keyss_;
        }

        const Param_keys& Solver::cunif_param_keys() const
        {
            expect(is_unified(), "Parameter keys are not unified.");
            return cunif_param_keys_wo_check();
        }

        const Param_keys& Solver::code_param_keys(Ode_id ode_id_) const
        {
            return code_param_keys(code_eval(ode_id_));
        }

        const Param_keys& Solver::code_param_keys(const Ode_eval& ode_eval_)
        {
            return ode_eval_.front().cparam_keys();
        }

        const Param_keys& Solver::cunif_param_keys_wo_check() const
        {
            return code_param_keys(code_eval());
        }

        const Param_key&
            Solver::code_param_key(Ode_id ode_id_, bool unified) const
        {
            return code_param_keys(ode_id_)[unified ? ode_id_
                                                    : def_ode_id];
        }

        Param_keys Solver::unify_param_keys(Param_keyss&& param_keyss_)
        {
            const int pkeys_size = param_keyss_.size();
            if (pkeys_size == 1 || all_equal(param_keyss_)) {
                return {move(param_keyss_.front())};
            }

            Param_keys param_keys_;
            param_keys_.reserve(pkeys_size*2);
            set<Param_key> pkeys_set;
            transform(param_keyss_, std::back_inserter(param_keys_),
                      [&pkeys_set](auto& pkeys){
                          auto pdt_key = move(pkeys.front());
                          expect(!pkeys_set.count(pdt_key),
                                 "First parameter key must be unique: "s
                                 + pdt_key);
                          pkeys_set.insert(pdt_key);
                          return pdt_key;
                      });
            bool has_t = false;
            for (auto&& pkeys : move(param_keyss_)) {
                std::for_each(std::make_move_iterator(std::begin(pkeys)+1),
                              std::make_move_iterator(std::end(pkeys)),
                              [&param_keys_, &pkeys_set, &has_t]
                              (auto&& pkey){
                                  if (pkey == "t") {
                                      has_t = true;
                                      return;
                                  }
                                  if (pkeys_set.emplace(pkey).second) {
                                      param_keys_.emplace_back(move(pkey));
                                  }
                              });
            }
            if (has_t) param_keys_.emplace_back("t");

            return param_keys_;
        }

        Real Solver::solve_ode(Dt_id dt_id_, Context context_,
                               Ode_id ode_id_) const
        {
            add_param_t(ode_has_param_t(ode_id_), context_, ode_id_);
            reset_traject(traject(ode_id_), context_);
            return eval_ode(ode_id_, dt_id_, move(context_));
        }

        State Solver::solve_odes(Dt_ids dt_ids_, Contexts contexts_) const
        {
            check_dt_ids(dt_ids_);
            reset_trajects(contexts_);
            const bool unified = is_unified()
                                 && (contexts_.size() == 1
                                     || all_equal(contexts_));
            if (unified) {
                return solve_unif_odes_wo_check(move(dt_ids_),
                                                move(contexts_.front()));
            }
            for_each(contexts_, std::begin(codes_eval()),
                    [this](Context& ctx, const Ode_eval& oeval){
                        const bool has_t = ode_has_param_t(oeval);
                        add_param_t(has_t, ctx, code_eval_id(oeval));
                    });
            return crop_result(eval_odes(move(dt_ids_),
                                         move(contexts_)));
        }

        State Solver::solve_unif_odes(Dt_ids dt_ids_,
                                      Context context_) const
        {
            expect(is_unified(), "Attempt to solve unified ODEs,"s
                                 + " but parameter keys are not unified.");
            check_dt_ids(dt_ids_);
            reset_unif_traject(context_);
            return solve_unif_odes_wo_check(move(dt_ids_),
                                            move(context_));
        }

        State&& Solver::crop_result(State&& result) const
        {
            result.resize(size());
            return move(result);
        }

        State Solver::solve_unif_odes_wo_check(Dt_ids dt_ids_,
                                               Context context_) const
        {
            add_param_t(has_unif_param_t(), context_);
            return crop_result(eval_unif_odes(move(dt_ids_),
                                              move(context_)));
        }

        State Solver::solve(string input) const
        {
            return solve(Expr(move(input)));
        }

        State Solver::solve(istream& is) const
        {
            return solve(Expr(is));
        }

        State Solver::solve(istream&& is) const
        {
            return solve(is);
        }

        State Solver::solve(Expr expr) const
        {
            expect(expr.size() == 2 && expr.is_deep(),
                   "Expected two expressions of chosen dt variants "s
                   + "and context(s) for ODEs.");

            Dt_ids dt_ids_ = expr.get_expr().transform_to_args<Dt_id>();

            Expr& ctx_expr = expr.get_expr();
            expect(ctx_expr.is_deep(),
                   "Expected subexpressions with context(s) for ODEs.");
            if (is_unified() && ctx_expr.size() == 1) {
                return solve_unif_odes(move(dt_ids_),
                                       Context(move(ctx_expr.get_expr())));
            }
            Contexts contexts_;
            contexts_.reserve(ctx_expr.size());
            transform(ctx_expr.transform_to_exprs(),
                      std::back_inserter(contexts_),
                      [](Expr&& e){ return Context(move(e)); });
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
            const int size_ = size();
            State res;
            res.reserve(size_);
            for (int i = 0; i < size_; i++) {
                res.emplace_back(eval_ode(i, dt_ids_[i],
                                          move(contexts_[i])));
            }
            return res;
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

        void Solver::eval_unif_odes_step(const Dt_ids& dt_ids_,
                                         State& dx,
                                         const State& x, Time t) const
        {
            eval_unif_odes_step(dt_ids_, std::begin(dx), x, t);
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
            return str;
        }

        string to_string(const Solver& rhs)
        {
            return (string)rhs;
        }

        ostream& operator <<(ostream& os, const Solver& rhs)
        {
            return (os << to_string(rhs));
        }

        Solver::Traject& Solver::traject(Ode_id ode_id_) const
        {
            return trajects()[ode_id_];
        }

        void Solver::init_unif_traject(Param_keys param_keys_) const
        {
            trajects().resize(1);
            init_traject(traject(), move(param_keys_), has_unif_param_t());
        }

        void Solver::init_trajects(Param_keyss param_keyss_) const
        {
            const int size_ = size();
            trajects().resize(size_);
            for (int i = 0; i < size_; i++) {
                init_traject(traject(i), move(param_keyss_[i]),
                             ode_has_param_t(i));
            }
        }

        void Solver::init_traject(Traject& traject_,
                                  Param_keys param_keys_,
                                  bool has_param_t) const
        {
            traject_.init(move(param_keys_), has_param_t);
        }

        void Solver::reset_unif_traject(const Context& context_) const
        {
            reset_traject(traject(), context_);
        }

        void Solver::reset_trajects(const Contexts& contexts_) const
        {
            for_each(trajects(), std::begin(contexts_),
                     bind(&Solver::reset_traject, this, _1, _2));
        }

        void Solver::reset_traject(Traject& traject_,
                                   const Context& context_) const
        {
            const size_t size_ =
                (context_.ct_distance()/cstep_size()+1)*1.02;
            traject_.reset(size_);
        }
    }
}
