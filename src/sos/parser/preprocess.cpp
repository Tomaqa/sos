#include "parser.hpp"

#include <iostream>

namespace SOS {
    const Parser::Preprocess::Reserved_macro_fs_map
        Parser::Preprocess::reserved_macro_fs_map{
        {"#def",    &Parser::Preprocess::exp_macro_def},
        {"#let",    &Parser::Preprocess::exp_macro_let},
        {"#if",     &Parser::Preprocess::exp_macro_if},
        {"#for",    &Parser::Preprocess::exp_macro_for},
    };

    string Parser::Preprocess::parse_input(string&& input)
    {
        istringstream iss(move(input));
        return parse_input(iss);
    }

    string Parser::Preprocess::parse_input(istream& is)
    {
        string str("");
        int size_ = istream_remain_size(is);
        if (size_ <= 0) return str;
        str.reserve(size_*1.2);
        char c;
        string tmp;
        tmp.reserve(40);
        is >> std::noskipws;
        while (is >> c) {
            switch (c) {
            default:
                str += c;
                break;
            case ';':
                getline(is, tmp);
                break;
            case '#':
                str += c;
                if (isspace(is.peek())) break;
                is >> std::skipws >> tmp;
                if (tmp != "define") {
                    str += tmp;
                }
                else {
                    getline(is, tmp);
                    str += "def" + tmp + " " + c + "enddef";
                }
                str += " ";
                is >> std::noskipws;
                break;
            }
        }
        return str;
    }

    void Parser::Preprocess::parse_expr(Expr& expr)
    {
        unsigned depth = 0;
        parse_nested_expr(expr, depth);
        std::cout << expr << std::endl;
        std::cout << _macros_map << std::endl;
    }

    bool Parser::Preprocess::is_macro_key(const Token& token)
    {
        return token[0] == '#';
    }

    bool Parser::Preprocess::is_arith_exp(const Token& token)
    {
        return (token == "$");
    }

    bool Parser::Preprocess::
        is_reserved_macro_key(const Macro_key& macro_key_)
    {
        return reserved_macro_fs_map.includes(macro_key_);
    }

    bool Parser::Preprocess::
        has_macro_key(const Macro_key& macro_key_) const
    {
        return cmacros_map().count(macro_key_) == 1;
    }

    void Parser::Preprocess::
        check_has_not_macro_key(const Macro_key& macro_key_) const
    {
        expect(!has_macro_key(macro_key_),
               "Macro named '"s + macro_key_ + "' "
               + "has already been defined.");
    }

    const Parser::Preprocess::Macro&
        Parser::Preprocess::cmacro(const Macro_key& macro_key_) const
    {
        return cmacros_map().at(macro_key_);
    }

    Parser::Preprocess::Macro&
        Parser::Preprocess::macro(const Macro_key& macro_key_)
    {
        return macros_map()[macro_key_];
    }

    const Parser::Preprocess::Macro_params&
        Parser::Preprocess::cmacro_params(const Macro_key& macro_key_) const
    {
        return get<0>(cmacro(macro_key_));
    }

    Parser::Preprocess::Macro_params&
        Parser::Preprocess::macro_params(const Macro_key& macro_key_)
    {
        return get<0>(macro(macro_key_));
    }

    const Parser::Preprocess::Macro_body&
        Parser::Preprocess::cmacro_body(const Macro_key& macro_key_) const
    {
        return get<1>(cmacro(macro_key_));
    }

    Parser::Preprocess::Macro_body&
        Parser::Preprocess::macro_body(const Macro_key& macro_key_)
    {
        return get<1>(macro(macro_key_));
    }

    void Parser::Preprocess::add_macro(const Macro_key& macro_key_,
                                       Macro_params macro_params_,
                                       Macro_body macro_body_)
    {
        macro(macro_key_) = make_tuple(move(macro_params_),
                                       move(macro_body_));
    }

    void Parser::Preprocess::parse_nested_expr(Expr& expr, unsigned depth)
    {
        while (expr) {
            if (expr.cpeek()->is_etoken()) {
                const Token& token = expr.cpeek_token();
                exp_token(expr, token, depth);
                continue;
            }
            Expr& subexpr = expr.get_expr();
            parse_nested_expr(subexpr, depth+1);
        }
        expr.reset_pos_to_valid();
    }

    void Parser::Preprocess::check_token(const Expr& expr,
                                         const Token& token,
                                         unsigned depth) const
    {
        expect(depth > 0,
               "Unexpected token at top level: '"s
               + token + "'");
    }

    void Parser::Preprocess::exp_token(Expr& expr,
                                       const Token& token,
                                       unsigned depth)
    {
        if (is_macro_key(token)) {
            Macro_key mkey = expr.extract_token();
            return exp_macro(expr, mkey, depth);
        }
        if (is_arith_exp(token)) {
            // expr.erase_at_pos();
            // arith_exp<double>(expr, depth);
            expr.erase_at_pos();
            arith_exp<double>(expr, depth);
        }
        check_token(expr, token, depth);
        expr.next();
    }

    void Parser::Preprocess::exp_macro(Expr& expr,
                                       const Macro_key& macro_key_,
                                       unsigned depth)
    {
        if (is_reserved_macro_key(macro_key_)) {
            return exp_reserved_macro(expr, macro_key_, depth);
        }
        exp_user_macro(expr, macro_key_, depth);
    }

    void Parser::Preprocess::
        exp_reserved_macro(Expr& expr, const Macro_key& macro_key_,
                           unsigned depth)
    {
        expect(depth == 0,
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        reserved_macro_fs_map[macro_key_](this, expr, depth);
    }

    void Parser::Preprocess::exp_macro_def(Expr& expr, unsigned depth)
    {
        Macro_key macro_key_ = expr.extract_token_check();
        check_has_not_macro_key(macro_key_);
        Expr params_expr;
        if (!expr.cpeek()->is_etoken()) {
            params_expr = expr.extract_expr();
        }
        Macro_params macro_params_ = params_expr.transform_to_tokens();

        Macro_body macro_body_;
        bool found = false;
        while (expr) {
            if (!expr.cpeek()->is_etoken()) {
                Expr subexpr = expr.extract_expr();
                macro_body_.add_new_expr(move(subexpr));
                continue;
            }
            Expr_token etoken = expr.extract_etoken();
            if (etoken.ctoken() == "#enddef") {
                found = true;
                break;
            }
            macro_body_.add_new_etoken(move(etoken));
        }
        expect(found, "#enddef not found.");

        add_macro(move(macro_key_), move(macro_params_), move(macro_body_));
    }

    void Parser::Preprocess::exp_macro_let(Expr& expr, unsigned depth)
    {

    }

    void Parser::Preprocess::exp_macro_if(Expr& expr, unsigned depth)
    {
        const bool cond = eval_token<double>(expr, depth);

        const auto keep_f = [](Expr& e){ e.next(); };
        const auto del_f = [](Expr& e){ e.erase_at_pos(); };
        const auto choose_f = [&keep_f, &del_f](bool keep){
            return (keep) ? keep_f : del_f;
        };

        bool keep = cond;
        auto f = choose_f(keep);
        while (expr) {
            if (expr.cpeek()->is_etoken()) {
                const Token& token = expr.cpeek_token();
                if (token == "#endif") {
                    expr.erase_at_pos();
                    break;
                }
                if (token == "#else") {
                    expr.erase_at_pos();
                    keep = !keep;
                    f = choose_f(keep);
                    continue;
                }
                if (keep) {
                    exp_token(expr, token, depth);
                }
            }
            f(expr);
        }
    }

    void Parser::Preprocess::exp_macro_for(Expr& expr, unsigned depth)
    {

    }

    void Parser::Preprocess::exp_user_macro(Expr& expr,
                                            const Macro_key& macro_key_,
                                            unsigned depth) const
    {
        expect(has_macro_key(macro_key_),
               "Macro was not defined: '"s
               + macro_key_ + "'");
        // ?
    }

    template <typename Arg>
    Arg Parser::Preprocess::eval_token(Expr& expr, unsigned depth)
    {
        Expr_token literal = expr.extract_etoken_check();
        if (!is_arith_exp(literal.ctoken())) {
            return literal.get_value_check<Arg>();
        }
        return eval_expr<Arg>(expr, depth);
    }

    template <typename Arg>
    Arg Parser::Preprocess::eval_expr(Expr& expr, unsigned depth)
    {
        Expr arith_expr = expr.extract_expr_check();
        parse_nested_expr(arith_expr, depth+1);
        return arith_expr.get_eval<Arg>()();
    }

    template <typename Arg>
    void Parser::Preprocess::arith_exp(Expr& expr, unsigned depth)
    {
        Arg arg = eval_expr<Arg>(expr, depth);
        // !
        // expr.add_new_etoken_at_pos(arg);
    }
}
