#ifndef ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
#define ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430

#include "ode.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

// ? teoreticky by slo taky kroky pocitat misto pomocti 'Eval'
// dynamickym vytvorenim C-funkce a jejim zkompilovanim ...

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
            using Param_keyss = vector<Param_keys>;

            class Context;
            using Contexts = vector<Context>;

            /// KONVENCE: posledni parametr je cas, aby to slo rychle overit
            // (pokud je obsazen)
            // + parametr derivovane funkce MUSI byt obsazen:
            // a) unifikovane klice: pozice [ode_id]
            // b) pozice [0]
            // nederivovane parametry musi byt az za temito; "t" je posledni
            // klice jsou bud sdilene mezi vsemi ODE, nebo jsou ruzne,
            // pak se lisi jestli je zadano voladni 'solve_unif_odes' nebo 'solve_odes'
            // Unifikace je ale vec konvence a zodpovednost uzivatele, hlidat to by bylo zbytecne slozite
            // Nevkladani klicu (vytvoreni z vyrazu) zatim nebudu vubec povolovat,
            // nenapada me k cemu by bylo dobre a je to nebezpecne

            Solver() = default;
            virtual ~Solver() = default;
            Solver(const Solver& rhs) = delete;
            Solver& operator =(const Solver& rhs) = delete;
            Solver(Solver&& rhs) = default;
            Solver& operator =(Solver&& rhs) = default;
            Solver(Odes_spec odes_spec_, Param_keyss param_keyss_);
            Solver(const string& input); // not implemented yet

            size_t size() const noexcept { return codes_spec().size(); }
            Time step_size() const noexcept { return _step_size; }
            void set_step_size(Time step_size_) noexcept
                { _step_size = step_size_; }
            void add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_);
            bool is_unified() const;
            void unify(); // not implemented yet

            virtual Real solve_ode(Dt_id dt_id_,
                                   Context context_,
                                   Ode_id ode_id_ = def_ode_id) const = 0;
            State solve_odes(Dt_ids dt_ids_, Contexts contexts_) const;
            State solve_unif_odes(Dt_ids dt_ids_, Context context_) const;

            explicit operator string () const;
            friend string to_string(const Solver& rhs)
                { return move((string)rhs); }
            friend ostream& operator <<(ostream& os, const Solver& rhs)
                { return (os << to_string(rhs)); }
        protected:
            using Dt_eval = Expr::Eval<Real>;
            using Ode_eval = vector<Dt_eval>;
            using Odes_eval = vector<Ode_eval>;

            static constexpr Ode_id def_ode_id = 0;

            const Odes_spec& codes_spec() const
                { return _odes_spec; }
            const Odes_eval& codes_eval() const
                { return _odes_eval; }
            Odes_spec& odes_spec()
                { return _odes_spec; }
            Odes_eval& odes_eval()
                { return _odes_eval; }

            static bool valid_keys(const Param_keys& param_keys_)
                { return param_keys_.size() >= 1; }
            static void check_keys(const Param_keys& param_keys_)
                { expect(valid_keys(param_keys_),
                         "Invalid parameter keys: "s
                         + to_string(param_keys_)); }
            static Ode_eval create_ode_eval(Ode_spec& ode_spec_,
                                     Param_keys param_keys_);

            virtual State eval_odes(Dt_ids&& dt_ids_,
                                    Contexts&& contexts_) const;
            virtual State eval_unif_odes(Dt_ids&& dt_ids_,
                                         Context&& context_) const;
            void eval_unif_odes_step(const Dt_ids& dt_ids_,
                                     State& dx, const State& x, Time t) const;
            State eval_unif_odes_step(const Dt_ids& dt_ids_,
                                      const State& x, Time t) const
                { State dx; eval_unif_odes_step(dt_ids_, dx, x, t);
                  return move(dx); }
            Real eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                               const State& x, Time t) const;
            void eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                               Real& dx, const State& x, Time t) const
                { dx = eval_ode_step(ode_eval_, dt_id_, x, t); }
        private:
            using Dt_eval_params = Dt_eval::Param_values;

            void modified();
            static bool dt_has_param_t(const Dt_eval& dt_eval_)
                { return dt_eval_.cparam_keys().back() == "t"; }
            static bool ode_has_param_t(const Ode_eval& ode_eval_)
                { return dt_has_param_t(ode_eval_.front()); }
            bool has_param_t(Ode_id ode_id_ = def_ode_id) const;

            Real eval_dt_step(const Dt_eval& dt_eval_,
                              const State& x, Time t) const;
            Real eval_dt_step(const Dt_eval& dt_eval_,
                              Dt_eval_params params) const
                { return dt_eval_(move(params)); }

            Time _step_size{1.0};
            Odes_spec _odes_spec;
            Odes_eval _odes_eval;
            mutable Flag _is_unified;
            mutable Flag _has_param_t;
        };

        class Solver::Context {
        public:
            Context() = delete;
            ~Context() = default;
            Context(const Context& rhs) = default;
            Context& operator =(const Context& rhs) = default;
            Context(Context&& rhs) = default;
            Context& operator =(Context&& rhs) = default;
            Context(Interval<Time> t_bounds_, State x_init_)
                : _t_bounds(move(t_bounds_)),
                  _x_init(move(x_init_)) { check_values(); }
            Context(const string& input);

            explicit operator string () const;
            friend string to_string(const Context& rhs)
                { return move((string)rhs); }
            friend ostream& operator <<(ostream& os, const Context& rhs)
                { return (os << to_string(rhs)); }
            friend bool operator ==(const Context& lhs, const Context& rhs);

            const Interval<Time>& ct_bounds() const { return _t_bounds; }
            Time ct_init() const { return ct_bounds().first; }
            Time ct_end() const { return ct_bounds().second; }
            const State& cx_init() const { return _x_init; }
        protected:
            void check_values() const;
            Interval<Time>& t_bounds() { return _t_bounds; }
            Time& t_init() { return t_bounds().first; }
            Time& t_end() { return t_bounds().second; }
            State& x_init() { return _x_init; }
        private:
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
