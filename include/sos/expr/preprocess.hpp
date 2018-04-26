#pragma once

#include "sos.hpp"
#include "expr.hpp"

#include <stack>

namespace SOS {
    using std::stack;

    class Expr::Preprocess {
    public:
        Preprocess(string input);
        Preprocess(istream& is);

        Expr parse();
    protected:
        using Macro_key = Token;
        using Macro_param_keys = Tokens;
        using Macro_param_key = Macro_param_keys::value_type;
        using Macro_body = Expr;
        using Macro = tuple<Macro_param_keys, Macro_body>;
        using Macros_map = map<Macro_key, Macro>;

        using Let_key = Macro_key;
        using Let_body = Macro_body;
        using Let = stack<Let_body>;
        using Lets_map = map<Let_key, Let>;

        using Reserved_macro_f = function<void(Preprocess*, Expr&, unsigned)>;
        using Reserved_macro_fs_map = Const_map<Macro_key, Reserved_macro_f>;

        using Exp_pos = iterator;

        static const Reserved_macro_fs_map reserved_macro_fs_map;

        Preprocess(Expr expr);

        static string parse_lines(string&& input);
        static string parse_lines(istream& is);

        static bool is_macro_key(const Token& token);
        static bool is_macro_key_char(char c);
        static void check_is_not_macro_key(const Token& token);
        static bool is_arith_expr(const Token& token);
        static bool is_arith_expr_char(char c);

        const Macros_map& cmacros_map() const          { return _macros_map; }
        Macros_map& macros_map()                       { return _macros_map; }
        static bool is_reserved_macro_key(const Macro_key& macro_key_);
        bool has_macro_key(const Macro_key& macro_key_) const;
        void check_has_not_macro_key(const Macro_key& macro_key_) const;
        const Macro& cmacro(const Macro_key& macro_key_) const;
        Macro& macro(const Macro_key& macro_key_);
        const Macro_param_keys&
            cmacro_param_keys(const Macro_key& macro_key_) const;
        Macro_param_keys& macro_param_keys(const Macro_key& macro_key_);
        static bool
            macro_param_keys_has_param_key(const Macro_param_keys&
                                               macro_param_keys_,
                                           const Macro_param_key&
                                               macro_param_key_);
        bool macro_has_param_key(const Macro_key& macro_key_,
                                 const Macro_param_key& macro_param_key_)
                                 const;
        const Macro_body& cmacro_body(const Macro_key& macro_key_) const;
        Macro_body& macro_body(const Macro_key& macro_key_);
        void add_macro(const Macro_key& macro_key_,
                       Macro_param_keys macro_param_keys_,
                       Macro_body macro_body_);

        const Lets_map& clets_map() const                { return _lets_map; }
        Lets_map& clets_map()                            { return _lets_map; }
        bool has_let_key(const Let_key& let_key_) const;
        void check_has_let_key(const Let_key& let_key_) const;
        const Let& clet(const Let_key& let_key_) const;
        Let& let(const Let_key& let_key_);
        const Let_body& clet_body(const Let_key& let_key_) const;
        Let_body& let_body(const Let_key& let_key_);
        void push_let_body(const Let_key& let_key_, Let_body let_body_);
        void pop_let_body(const Let_key& let_key_);

        void parse_nested_expr(Expr& expr, unsigned depth);
    private:
        using Eval_float_t = double;
        using Eval_int_t = int;
        using For_eval_t = Eval_int_t;

        union Eval_t {
            Eval_float_t f;
            Eval_int_t i;
        };
        using Eval_t_marked = pair<Eval_t, bool>;

        void check_token(const Expr& expr, unsigned depth) const;

        template <typename F> Exp_pos parse_and_return(Expr& expr, F f);
        void parse_token(Expr& expr, unsigned depth);
        Exp_pos exp_token(Expr& expr, unsigned depth);
        void parse_macro(Expr& expr, unsigned depth);
        void parse_reserved_macro(Expr& expr,
                                  const Macro_key& macro_key_,
                                  unsigned depth);
        void parse_macro_def(Expr& expr, unsigned depth);
        void parse_macro_let(Expr& expr, unsigned depth);
        void parse_macro_endlet(Expr& expr, unsigned depth);
        void parse_macro_if(Expr& expr, unsigned depth);
        void parse_macro_for(Expr& expr, unsigned depth);
        void parse_user_macro(Expr& expr,
                              Macro_key& macro_key_,
                              unsigned depth);
        Eval_t_marked parse_eval_arith_token(Expr& expr, unsigned depth);
        Eval_t_marked parse_eval_arith_expr(Expr& expr, unsigned depth);
        void parse_arith_expr(Expr& expr, unsigned depth);
        Exp_pos exp_arith_expr(Expr& expr, unsigned depth);

        void parse_token_single(Expr& expr, Token& token,
                                unsigned depth);
        void parse_token_multi(Expr& expr, Tokens& tokens, unsigned depth);
        Macro_body extract_macro_body(Expr& expr, Token end_token);
        void parse_user_macro_push_params(Expr& expr,
                                          const Macro_key& macro_key_,
                                          unsigned depth);
        void parse_user_macro_pop_params(Expr& expr,
                                         const Macro_key& macro_key_);
        static Tokens split_token(Token& token);

        template <typename Arg>
            static Eval_t_marked
                new_eval_marked_helper(Arg val, bool is_float);
        static Eval_t_marked new_eval_marked_float(Eval_float_t val);
        static Eval_t_marked new_eval_marked_int(Eval_int_t val);
        static Eval_t ceval_union(const Eval_t_marked& val_m);
        static Eval_t& eval_union(Eval_t_marked& val_m);
        static bool ceval_is_float(const Eval_t_marked& val_m);
        static bool& eval_is_float(Eval_t_marked& val_m);
        template <typename Arg>
            static Arg ceval_value(const Eval_t_marked& val_m);
        template <typename Arg>
            static Arg& eval_value(Eval_t_marked& val_m);
    private:
        Expr _expr;

        Macros_map _macros_map;
        Lets_map _lets_map;
        unsigned _macro_depth{0};
    };
}
