#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "smt.hpp"
#include "ode.hpp"
#include "expr.hpp"

namespace SOS {
    using namespace Util;

    class Parser {
    public:
        using Const_id = SMT::Const_id;
        using Const_ids = SMT::Const_ids;
        using Time_const_id = SMT::Time_const_id;
        using Time_const_ids = SMT::Time_const_ids;
        using Dt_const_id = SMT::Dt_const_id;
        using Init_const_id = SMT::Init_const_id;
        using Const_ids_entry = SMT::Const_ids_entry;
        using Const_ids_entries = SMT::Const_ids_entries;
        using Const_ids_row = SMT::Const_ids_row;
        using Const_ids_rows = SMT::Const_ids_rows;

        using Param_key = ODE::Param_key;
        using Param_keys = ODE::Param_keys;
        using Dt_key = Param_key;
        using Dt_keys = vector<Dt_key>;
        using Ode_key = Dt_key;
        using Ode_spec = ODE::Ode_spec;
        using Ode = tuple<Ode_key, Dt_keys, Ode_spec,
                          Param_keys, Const_ids_rows>;
        using Odes = vector<Ode>;

        using Time = ODE::Time;

        class Run;

        Parser()                                                    = default;
        ~Parser()                                                   = default;
        Parser(const Parser& rhs)                                   = default;
        Parser& operator =(const Parser& rhs)                       = default;
        Parser(Parser&& rhs)                                        = default;
        Parser& operator =(Parser&& rhs)                            = default;
        Parser(istream& is, bool preprocess_only = false);
        Parser(string input, bool preprocess_only = false);

        string preprocessed_input() const;
        const Odes& codes() const                            { return _odes; }
        string csmt_input() const;
        bool is_ode_step_set() const                 { return _ode_step_set; }
        Time code_step() const                           { return _ode_step; }

        static const Ode_key& code_ode_key(const Ode& ode_);
        static const Dt_keys& code_dt_keys(const Ode& ode_);
        static const Ode_spec& code_ode_spec(const Ode& ode_);
        static const Param_keys& code_param_keys(const Ode& ode_);
        static const Const_ids_rows& code_const_ids_rows(const Ode& ode_);
    protected:
        using Token = Expr::Token;

        using Dt_spec = ODE::Dt_spec;
        using Dts_spec_map = map<Dt_key, Dt_spec>;
        using Const_ids_map = map<Time_const_ids,
                                  pair<Const_ids_entries, int>>;
        using Odes_map_value = tuple<Dts_spec_map,
                                     Param_keys, Const_ids_map>;
        using Odes_map = map<Ode_key, pair<Odes_map_value, int>>;
        using Dt_keys_map_value = Ode_key;
        using Dt_keys_map = map<Dt_key, pair<Dt_keys_map_value, int>>;

        using Exprs = Expr::Exprs;

        static constexpr const char* smt_init_cmds =
            "(set-option :print-success false)\n"
            "(set-option :produce-models true)\n"
            "(define-sort Dt () Real)\n";
        static constexpr const char* def_smt_logic = "QF_UFLRA";

        Parser(Expr expr, bool preprocess_only = false);

        Odes& odes()                                         { return _odes; }
        const Ode& code(const Ode_key& ode_key_) const;
        Ode& ode(const Ode_key& ode_key_);

        static Ode_key& ode_ode_key(Ode& ode_);
        static Dt_keys& ode_dt_keys(Ode& ode_);
        static Ode_spec& ode_ode_spec(Ode& ode_);
        static Param_keys& ode_param_keys(Ode& ode_);
        static Const_ids_rows& ode_const_ids_rows(Ode& ode_);

        const Dt_keys& cdt_keys(const Ode_key& ode_key_) const;
        Dt_keys& dt_keys(const Ode_key& ode_key_);
        const Ode_spec& code_spec(const Ode_key& ode_key_) const;
        Ode_spec& ode_spec(const Ode_key& ode_key_);
        const Param_keys& cparam_keys(const Ode_key& ode_key_) const;
        Param_keys& param_keys(const Ode_key& ode_key_);
        const Const_ids_rows&
            cconst_ids_rows(const Ode_key& ode_key_) const;
        Const_ids_rows& const_ids_rows(const Ode_key& ode_key_);
        const Const_ids_row&
            cconst_ids_row(const Ode_key& ode_key_,
                           const Time_const_ids& time_consts) const;
        Const_ids_row&
            const_ids_row(const Ode_key& ode_key_,
                          const Time_const_ids& time_consts);
        const Const_ids_entries&
            cconst_ids_entries(const Ode_key& ode_key_,
                               const Time_const_ids& time_consts) const;
        Const_ids_entries&
            const_ids_entries(const Ode_key& ode_key_,
                              const Time_const_ids& time_consts);

        void parse();
        void parse_top_expr(Expr& expr);
        void parse_expr(Expr& expr);
        void maybe_parse_first_token(Expr& expr);
        void parse_token(Expr& expr);

        void parse_set_logic(Expr& expr);
        void add_set_logic_expr(Token token);
        void declare_ode(const Ode_key& ode_key_, Expr& keys_expr);
        void parse_define_dt(Expr& expr);
        void parse_define_ode_step(Expr& expr);
        void parse_int_ode(Expr& expr);

        static Const_id int_ode_identifier(const Ode_key& ode_key_);

        const Odes_map& codes_map() const                { return _odes_map; }
        Odes_map& odes_map()                             { return _odes_map; }
        bool has_ode_key(const Ode_key& ode_key_) const;
        void check_has_ode_key(const Ode_key& ode_key_) const;
        const Odes_map::mapped_type&
            codes_map_item(const Ode_key& ode_key_) const;
        Odes_map::mapped_type& odes_map_item(const Ode_key& ode_key_);
        const Odes_map_value&
            codes_map_value(const Ode_key& ode_key_) const;
        Odes_map_value& odes_map_value(const Ode_key& ode_key_);
        int code_key_idx(const Ode_key& ode_key_) const;
        int& ode_key_idx(const Ode_key& ode_key_);
        const Dts_spec_map& cdts_spec_map(const Ode_key& ode_key_) const;
        Dts_spec_map& dts_spec_map(const Ode_key& ode_key_);
        void add_ode_key(Ode_key ode_key_);

        const Dt_keys_map& cdt_keys_map() const       { return _dt_keys_map; }
        Dt_keys_map& dt_keys_map()                    { return _dt_keys_map; }
        bool has_dt_key(const Dt_key& dt_key_) const;
        void check_has_not_dt_key(const Dt_key& dt_key_) const;
        const Dt_keys_map::mapped_type&
            cdt_keys_map_item(const Dt_key& dt_key_) const;
        Dt_keys_map::mapped_type& dt_keys_map_item(const Dt_key& dt_key_);
        const Dt_keys_map_value&
            cdt_keys_map_value(const Dt_key& dt_key_) const;
        Dt_keys_map_value& dt_keys_map_value(const Dt_key& dt_key_);
        int cdt_key_idx(const Dt_key& dt_key_) const;
        int& dt_key_idx(const Dt_key& dt_key_);
        const Ode_key& code_key(const Dt_key& dt_key_) const;
        void add_dt_key(Ode_key ode_key_, Dt_key dt_key_);
        void add_dt_spec(const Ode_key& ode_key_,
                         const Dt_key& dt_key_, Dt_spec dt_spec_);

        Param_keys& param_keys_map(const Ode_key& ode_key_);
        void add_param_keys(const Ode_key& ode_key_, Expr& expr);

        const Const_ids_map& cconst_ids_map(const Ode_key& ode_key_) const;
        Const_ids_map& const_ids_map(const Ode_key& ode_key_);
        bool has_time_consts(const Ode_key& ode_key_,
                             const Time_const_ids& time_consts) const;
        const Const_ids_map::mapped_type&
            cconst_ids_map_item(const Ode_key& ode_key_,
                                const Time_const_ids& time_consts) const;
        Const_ids_map::mapped_type&
            const_ids_map_item(const Ode_key& ode_key_,
                               const Time_const_ids& time_consts);
        const Const_ids_entries&
            cconst_ids_map_entries(const Ode_key& ode_key_,
                                   const Time_const_ids& time_consts) const;
        Const_ids_entries&
            const_ids_map_entries(const Ode_key& ode_key_,
                                  const Time_const_ids& time_consts);
        int ctime_consts_idx(const Ode_key& ode_key_,
                             const Time_const_ids& time_consts) const;
        int& time_consts_idx(const Ode_key& ode_key_,
                             const Time_const_ids& time_consts);
        int csteps(const Ode_key& ode_key_) const;
        void add_time_consts(const Ode_key& ode_key_,
                             Time_const_ids time_consts);
        void add_const_ids_row(const Ode_key& ode_key_,
                               Time_const_ids time_consts,
                               Dt_const_id dt_const,
                               Init_const_id init_const,
                               Const_ids param_consts);

        const Exprs& csmt_exprs() const                 { return _smt_exprs; }
        Exprs& smt_exprs()                              { return _smt_exprs; }
        void add_smt_expr(Expr expr);
    private:
        Expr _expr;

        Odes _odes;
        Odes_map _odes_map;
        Dt_keys_map _dt_keys_map;

        string _smt_logic{def_smt_logic};
        bool _smt_logic_set{false};
        Exprs _smt_exprs;

        Time _ode_step;
        bool _ode_step_set{false};
    };
}
