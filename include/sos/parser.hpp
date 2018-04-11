#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "ode.hpp"
#include "expr.hpp"

namespace SOS {
    using namespace Util;
    using namespace ODE;

    class Parser {
    public:
        class Run;

        Parser()                                                    = default;
        ~Parser()                                                   = default;
        Parser(const Parser& rhs)                                   = default;
        Parser& operator =(const Parser& rhs)                       = default;
        Parser(Parser&& rhs)                                        = default;
        Parser& operator =(Parser&& rhs)                            = default;
        Parser(istream& is);
        Parser(const string& input);
        Parser(const Expr& expr);

        string smt_input() const;
    protected:
        static constexpr const char* smt_init_cmds
            = "(set-option :print-success false)\n"
              "(set-option :produce-models true)\n"
              "(set-logic QF_UFNRA)\n"
              "(define-sort Dt () Real)\n";

        static string preprocess_input(string input);
        static string preprocess_input(istream& is);
        void process_expr(Expr expr);
        void process_declare_ode(Expr&& expr);
        void process_define_dt(Expr&& expr);
        void process_define_ode_step(Expr&& expr);
        void process_assert(Expr&& expr);
        void process_int_ode(Expr&& expr);
    private:
        using Param_key = Expr::Token;
        using Param_keys = vector<Param_key>;
        using Dt_key = Param_key;
        using Dt_spec = Expr;
        using Ode_key = Dt_key;
        using Ode_spec = map<Dt_key, Dt_spec>;
        using Ode = pair<Ode_spec, Param_keys>;
        using Odes_spec = map<Ode_key, Ode>;

        using Dt_keys_map = map<Dt_key, Ode_key>;
        // using Dt_key_value = pair<Ode_key, Ode_spec::iterator>;
        // using Dt_keys_map = map<Dt_key, Dt_key_value>;

        using Smt_exprs = Expr::Exprs;

        const Odes_spec& codes_spec() const             { return _odes_spec; }
        Odes_spec& odes_spec()                          { return _odes_spec; }
        bool has_ode_key(const Ode_key& ode_key_) const;
        int ode_key_idx(const Ode_key& ode_key_) const;
        const Ode_spec& code_spec(const Ode_key& ode_key_) const;
        Ode_spec& ode_spec(const Ode_key& ode_key_);

        const Dt_keys_map& cdt_keys_map() const       { return _dt_keys_map; }
        Dt_keys_map& dt_keys_map()                    { return _dt_keys_map; }
        bool has_dt_key(const Dt_key& dt_key_) const;
        int dt_key_idx(const Dt_key& dt_key_) const;
        const Ode_key& code_key(const Dt_key& dt_key_) const;
        // const Ode_spec::iterator& code_spec_it(const Dt_key& dt_key_) const;

        const Param_keys& cparam_keys(const Ode_key& ode_key_) const;
        Param_keys& param_keys(const Ode_key& ode_key_);

        void add_dt_key(const Ode_key& ode_key_, Dt_key dt_key_);
        void set_dt_spec(const Dt_key& dt_key_, Dt_spec dt_spec_);

        const Smt_exprs& csmt_exprs() const             { return _smt_exprs; }
        Smt_exprs& smt_exprs()                          { return _smt_exprs; }
        void add_smt_expr(Expr&& expr);

        Odes_spec _odes_spec;
        Dt_keys_map _dt_keys_map;
        Smt_exprs _smt_exprs;
        Time _ode_step;
        bool _ode_step_set{false};
    };
}
