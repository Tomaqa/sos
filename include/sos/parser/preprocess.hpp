#pragma once

#include "sos.hpp"

namespace SOS {
    class Parser::Preprocess {
    public:
        static string parse_input(string&& input);
        static string parse_input(istream& is);
        void parse_expr(Expr& expr);
    protected:
        using Macro_key = Token;
        using Macro_params = Param_keys;
        using Macro_body = Expr;
        using Macro = tuple<Macro_params, Macro_body>;
        using Macros_map = map<Macro_key, Macro>;

        using Reserved_macro_f = function<void(Preprocess*, Expr&, unsigned)>;
        using Reserved_macro_fs_map = Const_map<Macro_key, Reserved_macro_f>;

        static const Reserved_macro_fs_map reserved_macro_fs_map;

        static bool is_macro_key(const Token& token);
        static bool is_arith_expr(const Token& token);

        const Macros_map& cmacros_map() const          { return _macros_map; }
        Macros_map& macros_map()                       { return _macros_map; }
        static bool is_reserved_macro_key(const Macro_key& macro_key_);
        bool has_macro_key(const Macro_key& macro_key_) const;
        void check_has_not_macro_key(const Macro_key& macro_key_) const;
        const Macro& cmacro(const Macro_key& macro_key_) const;
        Macro& macro(const Macro_key& macro_key_);
        const Macro_params& cmacro_params(const Macro_key& macro_key_) const;
        Macro_params& macro_params(const Macro_key& macro_key_);
        const Macro_body& cmacro_body(const Macro_key& macro_key_) const;
        Macro_body& macro_body(const Macro_key& macro_key_);
        void add_macro(const Macro_key& macro_key_,
                       Macro_params macro_params_,
                       Macro_body macro_body_);

        void parse_nested_expr(Expr& expr, unsigned depth);
    private:
        void check_token(const Expr& expr, unsigned depth) const;

        template <typename F> void parse_and_return(Expr& expr, F f);
        void parse_token(Expr& expr, unsigned depth);
        void parse_macro(Expr& expr, unsigned depth);
        void parse_reserved_macro(Expr& expr,
                                  const Macro_key& macro_key_,
                                  unsigned depth);
        void parse_macro_def(Expr& expr, unsigned depth);
        void parse_macro_let(Expr& expr, unsigned depth);
        void parse_macro_if(Expr& expr, unsigned depth);
        void parse_macro_for(Expr& expr, unsigned depth);
        void parse_user_macro(Expr& expr,
                              const Macro_key& macro_key_,
                              unsigned depth) const;
        template <typename Arg> Arg parse_eval_token(Expr& expr,
                                                     unsigned depth);
        template <typename Arg> Arg parse_eval_expr(Expr& expr,
                                                    unsigned depth);
        template <typename Arg> void parse_arith_expr(Expr& expr,
                                                      unsigned depth);
        template <typename Arg> void exp_arith_expr(Expr& expr,
                                                    unsigned depth);
    private:
        Macros_map _macros_map;
    };
}
