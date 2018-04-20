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

        using Reserved_macro_f = function<void(const Preprocess *const,
                                               Expr&, int&)>;
        using Reserved_macro_fs_map = Const_map<Macro_key, Reserved_macro_f>;

        static const Reserved_macro_fs_map reserved_macro_fs_map;

        Macros_map& macros_map() const                 { return _macros_map; }
        static bool is_macro_key(const Macro_key& macro_key_);
        static bool is_reserved_macro_key(const Macro_key& macro_key_);
        bool has_macro_key(const Macro_key& macro_key_) const;
        void check_has_not_macro_key(const Macro_key& macro_key_) const;
        Macro& macro(const Macro_key& macro_key_) const;
        Macro_params& macro_params(const Macro_key& macro_key_) const;
        Macro_body& macro_body(const Macro_key& macro_key_) const;
        void add_macro(const Macro_key& macro_key_,
                       Macro_params macro_params_,
                       Macro_body macro_body_) const;

        void parse_nested_expr(Expr& expr, unsigned depth);
    private:
        static Expr_token& get_etoken(Expr& expr, int& pos);
        static Token& get_token(Expr& expr, int& pos);
        static Expr& get_expr(Expr& expr, int& pos);
        static Expr_token& get_etoken_check(Expr& expr, int& pos);
        static Token& get_token_check(Expr& expr, int& pos);
        static Expr& get_expr_check(Expr& expr, int& pos);
        static void check_expr_pos(Expr& expr, int& pos);

        void parse_macro(Expr& expr, int& pos,
                         const Macro_key& macro_key_, bool is_top) const;
        void parse_top_macro(Expr& expr, int& pos,
                             const Macro_key& macro_key_) const;
        void parse_reserved_macro(Expr& expr, int& pos,
                                  const Macro_key& macro_key_) const;
        void parse_user_macro(Expr& expr, int& pos,
                              const Macro_key& macro_key_) const;
        void parse_macro_def(Expr& expr, int& pos) const;
        void parse_macro_let(Expr& expr, int& pos) const;
        void parse_macro_if(Expr& expr, int& pos) const;
        void parse_macro_for(Expr& expr, int& pos) const;
        template <typename Arg> static Arg parse_value(Expr& expr, int& pos);

    private:
        mutable Macros_map _macros_map;
    };
}
