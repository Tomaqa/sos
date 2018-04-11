#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "ode.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

namespace SOS {
    namespace ODE {
        using namespace Util;

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
            using Spec = pair<Odes_spec, Param_keyss>;

            class Context;
            using Contexts = vector<Context>;

            template <typename S> class Run;

            static constexpr Ode_id def_ode_id = 0;

            Solver()                                                = default;
            virtual ~Solver()                                       = default;
            Solver(const Solver& rhs)                               = default;
            Solver& operator =(const Solver& rhs)                   = default;
            Solver(Solver&& rhs)                                    = default;
            Solver& operator =(Solver&& rhs)                        = default;
            Solver(Odes_spec odes_spec_, Param_keyss param_keyss_);
            Solver(Odes_spec odes_spec_, Param_keys param_keys_);
            Solver(Ode_spec ode_spec_, Param_keys param_keys_);
            Solver(Spec spec);
            Solver(const string& input);
            Solver(const Expr& expr);

            size_t size() const noexcept       { return codes_spec().size(); }
            bool empty() const noexcept                { return size() == 0; }
            Time cstep_size() const noexcept            { return _step_size; }
            void set_step_size(Time step_size_) noexcept
                                                  { _step_size = step_size_; }

            void add_ode_spec(Ode_spec ode_spec_, Param_keys param_keys_);
            bool is_unified() const;
            bool ode_has_param_t(Ode_id ode_id_) const;
            bool has_unif_param_t() const;

            Param_keyss cparam_keyss() const;
            const Param_keys& cunif_param_keys() const;

            Real solve_ode(Dt_id dt_id_, Context context_,
                           Ode_id ode_id_ = def_ode_id) const;
            State solve_odes(Dt_ids dt_ids_, Contexts contexts_) const;
            State solve_unif_odes(Dt_ids dt_ids_, Context context_) const;
            State solve(const string& input) const;
            State solve(const Expr& expr) const;

            explicit operator string () const;
            friend string to_string(const Solver& rhs);
            friend ostream& operator <<(ostream& os, const Solver& rhs);
        protected:
            using Ode_eval = vector<Dt_eval>;
            using Odes_eval = vector<Ode_eval>;
            using Param_keys_ptr = Dt_eval::Param_keys_ptr;
            using Param_keys_ptrs = vector<Param_keys_ptr>;

            class Eval;

            static constexpr Dt_id def_dt_id = 0;
            static constexpr Time def_step_size = 1e-2;

            const Odes_spec& codes_spec() const         { return _odes_spec; }
            const Odes_eval& codes_eval() const         { return _odes_eval; }
            Odes_spec& odes_spec()                      { return _odes_spec; }
            Odes_eval& odes_eval()                      { return _odes_eval; }
            const Ode_spec& code_spec(Ode_id ode_id_ = def_ode_id) const
                                             { return codes_spec()[ode_id_]; }
            const Ode_eval& code_eval(Ode_id ode_id_ = def_ode_id) const
                                             { return codes_eval()[ode_id_]; }
            Ode_id code_spec_id(const Ode_spec& ode_spec_) const
                                        { return &ode_spec_ - &code_spec(0); }
            Ode_id code_eval_id(const Ode_eval& ode_eval_) const
                                        { return &ode_eval_ - &code_eval(0); }
            static const Dt_eval& cdt_eval(const Ode_eval& ode_eval_,
                                           Dt_id dt_id_ = def_dt_id)
                                                 { return ode_eval_[dt_id_]; }
            const Dt_eval& cdt_eval(Ode_id ode_id_ = def_ode_id,
                                    Dt_id dt_id_ = def_dt_id) const
                              { return cdt_eval(code_eval(ode_id_), dt_id_); }

            void check_empty(const Param_keyss& param_keyss_) const;
            static void check_ode_spec(const Ode_spec& ode_spec_);
            static bool valid_ode_spec(const Ode_spec& ode_spec_);
            bool check_param_keyss(const Param_keyss& param_keyss_) const;
            static void check_param_keys(const Param_keys& param_keys_);
            static bool valid_keys(const Param_keys& param_keys_);
            void check_dt_ids(const Dt_ids& dt_ids_) const;

            static Param_keys_ptr new_param_keys(Param_keys&& param_keys_);
            void add_odes_eval(Param_keyss&& param_keyss_);
            void add_unif_odes_eval(Param_keys&& param_keys_);
            template <typename Keys> void
                add_ode_eval(Ode_spec& ode_spec_, Keys&& keys_);
            static Ode_eval create_ode_eval(Ode_spec& ode_spec_,
                                            Param_keys param_keys_);
            static Ode_eval create_ode_eval(Ode_spec& ode_spec_,
                                            Param_keys_ptr param_keys_ptr_);

            State solve_unif_odes_wo_check(Dt_ids dt_ids_,
                                           Context context_) const;
            virtual Real eval_ode(Ode_id ode_id_, Dt_id dt_id_,
                                  Context&& context_) const               = 0;
            virtual State eval_odes(Dt_ids&& dt_ids_,
                                    Contexts&& contexts_) const;
            virtual State eval_unif_odes(Dt_ids&& dt_ids_,
                                         Context&& context_) const        = 0;

            template <typename OutputIt>
                void eval_unif_odes_step(const Dt_ids& dt_ids_,
                                         OutputIt dx_it,
                                         const State& x, Time t) const;
            State eval_unif_odes_step(const Dt_ids& dt_ids_,
                                      const State& x, Time t) const;
            void eval_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                               Real& dx, const State& x, Time t) const;
            Real eval_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                               const State& x, Time t) const;
            void eval_unif_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                    Real& dx, const State& x, Time t) const;
            Real eval_unif_ode_step(Ode_id ode_id_, Dt_id dt_id_,
                                    const State& x, Time t) const;
        private:
            using State_f = function<const State&(const State&, Time)>;
            using State_fs = vector<State_f>;

            void set_odes_eval(Param_keyss&& param_keyss_);
            void parse_odes_spec(const Expr& expr);
            static Param_keyss parse_param_keyss(const Expr& expr);
            static Param_keys parse_param_keys(const Expr& expr);

            void modified();
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

            State_fs& state_fs() const                   { return _state_fs; }
            State_f& state_f(Ode_id ode_id_ = def_ode_id) const;
            void set_state_f(bool has_t, Ode_id ode_id_ = def_ode_id) const;
            static State_f get_state_f(bool has_t);
            const State& state(const State& x, Time t,
                               Ode_id ode_id_ = def_ode_id) const;
            static void context_add_param_t(bool has_t, Context& context_);
            void add_param_t(bool has_t, Context& context_,
                             Ode_id ode_id_ = def_ode_id) const;

            Real eval_dt_step(const Dt_eval& dt_eval_, Ode_id state_id,
                              const State& x, Time t) const;

            Time _step_size{def_step_size};
            Odes_spec _odes_spec;
            Odes_eval _odes_eval;
            mutable Flag _is_unified;
            mutable Flag _has_param_t;
            mutable State_fs _state_fs;
        };
    }
}