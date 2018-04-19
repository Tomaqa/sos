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
        using Dt_key = Param_key;
        using Dt_keys = vector<Dt_key>;
        using Const_id = Param_key;
        using Const_ids = vector<Const_id>;
        using Const_ids_row = tuple<Const_id, Const_id,
                                    pair<Const_id, Const_id>,
                                    Const_ids>;
        using Const_ids_rows = vector<Const_ids_row>;
        using Ode_key = Dt_key;
        using Ode = tuple<Ode_key, Dt_keys, Ode_spec,
                          Param_keys, Const_ids_rows>;
        using Odes = vector<Ode>;

        class Run;

        Parser()                                                    = default;
        ~Parser()                                                   = default;
        Parser(const Parser& rhs)                                   = default;
        Parser& operator =(const Parser& rhs)                       = default;
        Parser(Parser&& rhs)                                        = default;
        Parser& operator =(Parser&& rhs)                            = default;
        Parser(istream& is);
        Parser(string input);
        Parser(Expr expr);

        const Odes& codes() const                            { return _odes; }
        string csmt_input() const;
        bool is_ode_step_set() const                 { return _ode_step_set; }
        Time code_step() const                           { return _ode_step; }
    protected:
        static constexpr const char* smt_init_cmds =
            "(set-option :print-success false)\n"
            "(set-option :produce-models true)\n"
            "(set-logic QF_UFNRA)\n"
            //! "(set-logic QF_UFLRA)\n"
            "(define-sort Dt () Real)\n";

        Odes& odes()                                         { return _odes; }
        const Ode& code(const Ode_key& ode_key_) const;
        Ode& ode(const Ode_key& ode_key_);
        const Dt_keys& cdt_keys(const Ode_key& ode_key_) const;
        Dt_keys& dt_keys(const Ode_key& ode_key_);
        const Ode_spec& code_spec(const Ode_key& ode_key_) const;
        Ode_spec& ode_spec(const Ode_key& ode_key_);
        const Param_keys& cparam_keys(const Ode_key& ode_key_) const;
        Param_keys& param_keys(const Ode_key& ode_key_);
        const Const_ids_rows& cconst_ids(const Ode_key& ode_key_) const;
        Const_ids_rows& const_ids(const Ode_key& ode_key_);

        static string preprocess_input(string&& input);
        static string preprocess_input(istream& is);
        void preprocess_expr(Expr& expr);

        void parse_expr(Expr& expr);
        void declare_ode(const Ode_key& ode_key_, Expr& keys_expr);
        void parse_define_dt(Expr& expr);
        void parse_define_ode_step(Expr& expr);
        void parse_assert(Expr& expr);
        void parse_int_ode(Expr& expr);

        static Const_id int_ode_identifier(const Ode_key& ode_key_);
    private:
        using Token = Expr::Token;

        using Dts_spec_map = map<Dt_key, Dt_spec>;
        using Odes_map_value = tuple<Dts_spec_map,
                                     Param_keys, Const_ids_rows>;
        using Odes_map = map<Ode_key, pair<Odes_map_value, int>>;
        using Dt_keys_map_value = Ode_key;
        using Dt_keys_map = map<Dt_key, pair<Dt_keys_map_value, int>>;

        using Exprs = Expr::Exprs;
        // using Parser_exprs = Exprs;

        using Macro_key = Token;
        using Macro_params = Param_keys;
        using Macro_body = string;
        using Macro = tuple<Macro_params, Macro_body>;
        using Macros_map = map<Macro_key, Macro>;

        using Reserved_macro_f = function<void(const Parser *const,
                                               Expr&, int&)>;
        using Reserved_macro_fs_map = Const_map<Macro_key, Reserved_macro_f>;

        using Let_key = Macro_key;
        using Let_body = Macro_body;
        using Lets_map = map<Let_key, Let_body>;

        static const Reserved_macro_fs_map reserved_macro_fs_map;

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

        Const_ids_rows& const_ids_map(const Ode_key& ode_key_);
        int csteps(const Ode_key& ode_key_) const;
        void add_const_ids_row(const Ode_key& ode_key_,
                               Const_id dt_const, Const_id init_const,
                               pair<Const_id, Const_id> init_t_consts,
                               Const_ids param_consts);

        const Exprs& csmt_exprs() const                 { return _smt_exprs; }
        Exprs& smt_exprs()                              { return _smt_exprs; }
        void add_smt_expr(Expr expr);

        Macros_map& macros_map() const                 { return _macros_map; }
        static bool is_macro_key(const Macro_key& macro_key_);
        static bool is_reserved_macro_key(const Macro_key& macro_key_);
        bool has_macro_key(const Macro_key& macro_key_) const;
        void check_has_not_macro_key(const Macro_key& macro_key_) const;
        Macro& macro(const Macro_key& macro_key_) const;
        Macro_params& macro_params(const Macro_key& macro_key_) const;
        Macro_body& macro_body(const Macro_key& macro_key_) const;
        void add_macro_key(const Macro_key& macro_key_) const;
        void add_macro(const Macro_key& macro_key_,
                       Macro_params macro_params_,
                       Macro_body macro_body_) const;

        void preprocess_nested_expr(Expr& expr, int& pos, unsigned depth);
        void parse_macro(Expr& expr, int& pos,
                         const Macro_key& macro_key_, bool is_top) const;
        void parse_top_macro(Expr& expr, int& pos,
                             const Macro_key& macro_key_) const;
        void parse_reserved_macro(Expr& expr, int& pos,
                                  const Macro_key& macro_key_) const;
        void parse_user_macro(Expr& expr, int& pos,
                              const Macro_key& macro_key_) const;
        void parse_macro_def(Expr& expr, int& pos) const
                                        { parse_macro_def_helper(expr, pos); }
        void parse_macro_define(Expr& expr, int& pos) const
                                  { parse_macro_def_helper(expr, pos, true); }
        void parse_macro_def_helper(Expr& expr, int& pos,
                                    bool one_line = false) const;
        void parse_macro_let(Expr& expr, int& pos) const;
        void parse_macro_if(Expr& expr, int& pos) const
                                         { parse_macro_if_helper(expr, pos); }
        void parse_macro_ite(Expr& expr, int& pos) const
                                   { parse_macro_if_helper(expr, pos, true); }
        void parse_macro_if_helper(Expr& expr, int& pos,
                                   bool else_branch = false) const;
        void parse_macro_for(Expr& expr, int& pos) const;
        template <typename Arg> Arg parse_arith_exp(Expr& expr) const;

        // Parser_exprs& parser_exprs() const           { return _parser_exprs; }
        // void add_parser_expr(Expr expr) const;

        //! there may be some issue with move operations ?
        //! I've experienced some ..
        Odes _odes;
        Odes_map _odes_map;
        Dt_keys_map _dt_keys_map;

        Exprs _smt_exprs;

        Time _ode_step;
        bool _ode_step_set{false};

        // mutable Parser_exprs _parser_exprs;
        mutable Macros_map _macros_map;
        mutable Lets_map _lets_map;
    };
}
