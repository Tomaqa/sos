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
        using Param_key = Expr::Token;
        using Param_keys = vector<Param_key>;
        using Dt_spec = Expr;
        using Dt_key = Param_key;
        using Dts_spec_map = map<Dt_key, Dt_spec>;
        using Const_id = Param_key;
        using Const_ids_row = tuple<Const_id, Const_id,
                                    pair<Const_id, Const_id>,
                                    vector<Const_id>>;
        using Const_ids = vector<Const_ids_row>;
        using Ode = tuple<Dts_spec_map, Param_keys, Const_ids>;
        using Ode_key = Dt_key;
        using Odes_map = map<Ode_key, Ode>;

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

        const Odes_map& codes_map() const                { return _odes_map; }
        string csmt_input() const;
    protected:
        static constexpr const char* smt_init_cmds
            = "(set-option :print-success false)\n"
              "(set-option :produce-models true)\n"
              // "(set-option :produce-proofs true)\n"
              // "(set-logic QF_UFNRA)\n"
              "(set-logic QF_UFLRA)\n"
              "(define-sort Dt () Real)\n";

        static string preprocess_input(string input);
        static string preprocess_input(istream& is);
        void process_expr(Expr expr);
        void process_declare_ode(Expr&& expr);
        void process_define_dt(Expr&& expr);
        void process_define_ode_step(Expr&& expr);
        void process_assert(Expr& expr);
        void process_int_ode(Expr& expr);

        static Expr::Token int_ode_identifier(const Ode_key& ode_key_);
    private:
        using Dt_keys_map = map<Dt_key, Ode_key>;

        using Smt_exprs = Expr::Exprs;

        Odes_map& odes_map()                             { return _odes_map; }
        bool has_ode_key(const Ode_key& ode_key_) const;
        void check_has_ode_key(const Ode_key& ode_key_) const;
        int ode_key_idx(const Ode_key& ode_key_) const;
        const Dts_spec_map& cdts_spec_map(const Ode_key& ode_key_) const;
        Dts_spec_map& dts_spec_map(const Ode_key& ode_key_);

        const Dt_keys_map& cdt_keys_map() const       { return _dt_keys_map; }
        Dt_keys_map& dt_keys_map()                    { return _dt_keys_map; }
        bool has_dt_key(const Dt_key& dt_key_) const;
        void check_has_dt_key(const Dt_key& dt_key_) const;
        int dt_key_idx(const Dt_key& dt_key_) const;
        const Ode_key& code_key(const Dt_key& dt_key_) const;
        void add_dt_key(const Ode_key& ode_key_, Dt_key dt_key_);
        void set_dt_spec(const Dt_key& dt_key_, Dt_spec dt_spec_);

        const Param_keys& cparam_keys(const Ode_key& ode_key_) const;
        Param_keys& param_keys(const Ode_key& ode_key_);

        const Const_ids& cconst_ids(const Ode_key& ode_key_) const;
        Const_ids& const_ids(const Ode_key& ode_key_);
        int csteps(const Ode_key& ode_key_) const;
        void add_const_ids_row(const Ode_key& ode_key_,
                               Const_id&& dt_const, Const_id&& init_const,
                               pair<Const_id, Const_id>&& init_t_consts,
                               vector<Const_id>&& param_consts);

        const Smt_exprs& csmt_exprs() const             { return _smt_exprs; }
        Smt_exprs& smt_exprs()                          { return _smt_exprs; }
        void add_smt_expr(Expr&& expr);

        Odes_map _odes_map;
        Dt_keys_map _dt_keys_map;
        Smt_exprs _smt_exprs;
        Time _ode_step;
        bool _ode_step_set{false};
    };
}
