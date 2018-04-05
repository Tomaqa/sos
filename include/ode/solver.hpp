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
            using Dt_eval = Expr::Eval<Real>;
            using Ode_spec = vector<Dt_spec>;
            using Odes_spec = vector<Ode_spec>;
            using Dt_id = int;
            using Ode_id = int;
            using Dt_ids = vector<Dt_id>;
            using Param_key = Dt_eval::Param_key;
            using Param_keys = Dt_eval::Param_keys;
            using Param_keyss = vector<Param_keys>;

            class Context;
            using Contexts = vector<Context>;

            static constexpr Ode_id def_ode_id = 0;

            /// KONVENCE: posledni parametr je cas, aby to slo rychle overit
            // (pokud je obsazen)
            // + parametr derivovane funkce MUSI byt obsazen:
            // a) unifikovane klice: pozice [ode_id]
            // b) jinak: pozice [def_ode_id]
            // nederivovane parametry musi byt az za temito; "t" je posledni

            Solver()                                                = default;
            virtual ~Solver()                                       = default;
            Solver(const Solver& rhs)                               = default;
            Solver& operator =(const Solver& rhs)                   = default;
            Solver(Solver&& rhs)                                    = default;
            Solver& operator =(Solver&& rhs)                        = default;
            Solver(Odes_spec odes_spec_, Param_keyss param_keyss_);
            Solver(const string& input); // not implemented yet

            size_t size() const noexcept       { return codes_spec().size(); }
            bool empty() const noexcept                { return size() == 0; }
            Time step_size() const noexcept             { return _step_size; }
            void set_step_size(Time step_size_) noexcept
                                                  { _step_size = step_size_; }

            void add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_);
            bool is_unified(bool eval_if_unknown = true) const;
            void unify(); // not implemented yet
            bool has_param_t() const;

            Param_keyss cparam_keyss() const;
            const Param_keys& cunif_param_keys() const;

            virtual Real solve_ode(Dt_id dt_id_,
                                   Context context_,
                                   Ode_id ode_id_ = def_ode_id) const     = 0;
            State solve_odes(Dt_ids dt_ids_, Contexts contexts_) const;
            State solve_unif_odes(Dt_ids dt_ids_, Context context_) const;

            explicit operator string () const;
            friend string to_string(const Solver& rhs);
            friend ostream& operator <<(ostream& os, const Solver& rhs);
        protected:
            using Ode_eval = vector<Dt_eval>;
            using Odes_eval = vector<Ode_eval>;
            using Param_keys_ptr = Dt_eval::Param_keys_ptr;
            using Param_keys_ptrs = vector<Param_keys_ptr>;

            const Odes_spec& codes_spec() const         { return _odes_spec; }
            const Odes_eval& codes_eval() const         { return _odes_eval; }
            Odes_spec& odes_spec()                      { return _odes_spec; }
            Odes_eval& odes_eval()                      { return _odes_eval; }
            const Ode_spec& code_spec(Ode_id ode_id_ = def_ode_id) const
                                             { return codes_spec()[ode_id_]; }
            const Ode_eval& code_eval(Ode_id ode_id_ = def_ode_id) const
                                             { return codes_eval()[ode_id_]; }

            bool check_param_keyss(const Param_keyss& param_keyss_);
            static void check_param_keys(const Param_keys& param_keys_);
            static bool valid_keys(const Param_keys& param_keys_);

            static Param_keys_ptr new_param_keys(Param_keys&& param_keys_);
            void add_odes_eval(Param_keyss&& param_keyss_);
            void add_unif_odes_eval(Param_keys&& param_keys_);
            template <typename Keys> void
                add_ode_eval(Ode_spec& ode_spec_, Keys&& keys_);
            static Ode_eval create_ode_eval(Ode_spec& ode_spec_,
                                            Param_keys param_keys_);
            static Ode_eval create_ode_eval(Ode_spec& ode_spec_,
                                            Param_keys_ptr param_keys_ptr_);

            virtual State eval_odes(Dt_ids&& dt_ids_,
                                    Contexts&& contexts_) const;
            virtual State eval_unif_odes(Dt_ids&& dt_ids_,
                                         Context&& context_) const;
            void eval_unif_odes_step(const Dt_ids& dt_ids_,
                                     State& dx, const State& x, Time t) const;
            State eval_unif_odes_step(const Dt_ids& dt_ids_,
                                      const State& x, Time t) const;
            void eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                               Real& dx, const State& x, Time t) const;
            Real eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                               const State& x, Time t) const;
        private:
            using Dt_eval_params = Dt_eval::Param_values;

            void modified();
            bool has_param_t(Ode_id ode_id_) const;
            static bool ode_has_param_t(const Ode_eval& ode_eval_);
            static bool dt_has_param_t(const Dt_eval& dt_eval_);

            const Param_keys& code_param_keys(Ode_id ode_id_) const;
            static const Param_keys&
                code_param_keys(const Ode_eval& ode_eval_);
            const Param_keys& cunif_param_keys_wo_check() const;
            const Param_key& code_param_key(Ode_id ode_id_,
                                            bool unified) const;
            const Param_key& code_param_key(Ode_id ode_id_) const
                             { return code_param_key(ode_id_, is_unified()); }

            Real eval_dt_step(const Dt_eval& dt_eval_,
                              const State& x, Time t) const;
            Real eval_dt_step(const Dt_eval& dt_eval_,
                              Dt_eval_params params) const;

            Time _step_size{1.0};
            Odes_spec _odes_spec;
            Odes_eval _odes_eval;
            mutable Flag _is_unified;
            mutable Flag _has_param_t;
        };

        class Solver::Context {
        public:
            Context()                                                = delete;
            ~Context()                                              = default;
            Context(const Context& rhs)                             = default;
            Context& operator =(const Context& rhs)                 = default;
            Context(Context&& rhs)                                  = default;
            Context& operator =(Context&& rhs)                      = default;
            Context(Interval<Time> t_bounds_, State x_init_);
            Context(const string& input);

            explicit operator string () const;
            friend string to_string(const Context& rhs);
            friend ostream& operator <<(ostream& os, const Context& rhs);

            friend bool operator ==(const Context& lhs, const Context& rhs);

            const Interval<Time>& ct_bounds() const      { return _t_bounds; }
            Time ct_init() const                 { return ct_bounds().first; }
            Time ct_end() const                 { return ct_bounds().second; }
            const State& cx_init() const                   { return _x_init; }
        protected:
            void check_values() const;

            Interval<Time>& t_bounds()                   { return _t_bounds; }
            Time& t_init()                        { return t_bounds().first; }
            Time& t_end()                        { return t_bounds().second; }
            State& x_init()                                { return _x_init; }
        private:
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}

#endif // ___SOS_SOLVER_H_OUDH9GH34798GH949T938HJ3409FG430
