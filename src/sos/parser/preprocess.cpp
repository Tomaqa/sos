#include "parser.hpp"

#include <iostream>

namespace SOS {
    const Parser::Preprocess::Reserved_macro_fs_map
        Parser::Preprocess::reserved_macro_fs_map{
        {"#def",    &Parser::Preprocess::parse_macro_def},
        {"#let",    &Parser::Preprocess::parse_macro_let},
        {"#if",     &Parser::Preprocess::parse_macro_if},
        {"#for",    &Parser::Preprocess::parse_macro_for},
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
    }

    bool Parser::Preprocess::is_macro_key(const Macro_key& macro_key_)
    {
        return macro_key_[0] == '#';
    }

    bool Parser::Preprocess::
        is_reserved_macro_key(const Macro_key& macro_key_)
    {
        return reserved_macro_fs_map.includes(macro_key_);
    }

    bool Parser::Preprocess::
        has_macro_key(const Macro_key& macro_key_) const
    {
        return macros_map().count(macro_key_) == 1;
    }

    void Parser::Preprocess::
        check_has_not_macro_key(const Macro_key& macro_key_) const
    {
        expect(!has_macro_key(macro_key_),
               "Macro named '"s + macro_key_ + "' "
               + "has already been defined.");
    }

    Parser::Preprocess::Macro&
        Parser::Preprocess::macro(const Macro_key& macro_key_) const
    {
        return macros_map()[macro_key_];
    }

    Parser::Preprocess::Macro_params&
        Parser::Preprocess::macro_params(const Macro_key& macro_key_) const
    {
        return get<0>(macro(macro_key_));
    }

    Parser::Preprocess::Macro_body&
        Parser::Preprocess::macro_body(const Macro_key& macro_key_) const
    {
        return get<1>(macro(macro_key_));
    }

    void Parser::Preprocess::add_macro(const Macro_key& macro_key_,
                                       Macro_params macro_params_,
                                       Macro_body macro_body_) const
    {
        macro(macro_key_) = make_tuple(move(macro_params_),
                                       move(macro_body_));
    }

    // Expr_token& Parser::Preprocess::get_etoken(Expr& expr, int& pos)
    // {
    //     return expr.to_etoken(pos++);
    // }

    // Parser::Token& Parser::Preprocess::get_token(Expr& expr, int& pos)
    // {
    //     return expr.to_token(pos++);
    // }

    // Expr& Parser::Preprocess::get_expr(Expr& expr, int& pos)
    // {
    //     return expr.to_expr(pos++);
    // }

    // Expr_token& Parser::Preprocess::get_etoken_check(Expr& expr, int& pos)
    // {
    //     check_expr_pos(expr, pos);
    //     return expr.to_etoken_check(pos++);
    // }

    // Parser::Token& Parser::Preprocess::get_token_check(Expr& expr, int& pos)
    // {
    //     check_expr_pos(expr, pos);
    //     return expr.to_token_check(pos++);
    // }

    // Expr& Parser::Preprocess::get_expr_check(Expr& expr, int& pos)
    // {
    //     check_expr_pos(expr, pos);
    //     return expr.to_expr_check(pos++);
    // }

    // void Parser::Preprocess::check_expr_pos(Expr& expr, int& pos)
    // {
    //     expect(pos < (int)expr.size(),
    //            "Unexpected end of expression.");
    // }

    void Parser::Preprocess::parse_nested_expr(Expr& expr, unsigned depth)
    {
        // int pos = 0;
        // const int size_ = expr.size();
        // const bool is_top = (depth == 0);
        // while (pos < size_) {
        //     if (expr[pos]->is_etoken()) {
        //         const Macro_key& macro_key_ = get_token(expr, pos);
        //         if (is_macro_key(macro_key_)) {
        //             parse_macro(expr, pos, macro_key_, is_top);
        //             continue;
        //         }
        //         expect(!is_top,
        //                "Unexpected token at top level: '"s
        //                + macro_key_ + "'");
        //         continue;
        //     }
        //     Expr& subexpr = get_expr(expr, pos);
        //     parse_nested_expr(subexpr, depth+1);
        // }
    }

    void Parser::Preprocess::parse_macro(Expr& expr, int& pos,
                                         const Macro_key& macro_key_,
                                         bool is_top) const
    {
        // if (is_top) {
        //     return parse_top_macro(expr, pos, macro_key_);
        // }
        // expect(!is_reserved_macro_key(macro_key_),
        //        "Unexpected nested reserved macro: '"s
        //        + macro_key_ + "'");
        // parse_user_macro(expr, pos, macro_key_);
    }

    void Parser::Preprocess::
        parse_top_macro(Expr& expr, int& pos,
                        const Macro_key& macro_key_) const
    {
        // if (is_reserved_macro_key(macro_key_)) {
        //     return parse_reserved_macro(expr, pos, macro_key_);
        // }
        // parse_user_macro(expr, pos, macro_key_);
    }

    void Parser::Preprocess::
        parse_reserved_macro(Expr& expr, int& pos,
                             const Macro_key& macro_key_) const
    {
        reserved_macro_fs_map[macro_key_](this, expr, pos);
    }

    void Parser::Preprocess::
        parse_user_macro(Expr& expr, int& pos,
                         const Macro_key& macro_key_) const
    {
        expect(has_macro_key(macro_key_),
               "Macro was not defined: '"s
               + macro_key_ + "'");
        // ?
    }

    void Parser::Preprocess::parse_macro_def(Expr& expr, int& pos) const
    {
        // const int expr_size = expr.size();
        // const int def_pos = pos-1;
        // Macro_key& macro_key_ = get_token_check(expr, pos);
        // check_has_not_macro_key(macro_key_);
        // Expr params_expr;
        // if (!expr[pos]->is_etoken()) {
        //     params_expr = move(get_expr(expr, pos));
        // }
        // Macro_params macro_params_ = params_expr.transform_to_tokens();
        // int body_pos = pos;
        // const int def_size = body_pos-def_pos;
        // std::cout << macro_key_ << std::endl;
        // std::cout << macro_params_ << std::endl;

        // // Macro_body macro_body_;
        // // macro_body_.reserve(16);
        // while (true) {
        //     expect(pos < expr_size, "#enddef not found.");
        //     if (!expr[pos]->is_etoken()) {
        //         // macro_body_.add_new_expr(get_expr(expr, pos));
        //         // macro_body_.add_new_expr(move(get_expr(expr, pos)));
        //         continue;
        //     }
        //     Expr_token& etoken = get_etoken(expr, pos);
        //     if (etoken.ctoken() == "#enddef") break;
        //     // macro_body_.add_new_etoken(etoken);
        //     // macro_body_.add_new_etoken(move(etoken));
        // }
        // int end_pos = pos-1;
        // const int end_size = end_pos-body_pos+1;
        // const int body_size = end_size-1;
        // Macro_body macro_body_;
        // macro_body_.reserve(body_size);
        // std::move(std::begin(expr)+body_pos,
        //           std::begin(expr)+body_pos+body_size,
        //           std::back_inserter(macro_body_));

        // std::cout << macro_body_ << std::endl;
        // std::cout << def_pos << " " << body_pos << " " << end_pos << std::endl;
        // std::cout << def_size << " " << body_size << " " << end_size << std::endl;
        // // expr.erase_places(def_pos, pos-def_pos);
        // expr.erase_places(def_pos, def_size+end_size);
        // // pos -=
        // std::cout << "Ziju" << std::endl;

        // add_macro(macro_key_, move(macro_params_), move(macro_body_));
    }

    void Parser::Preprocess::parse_macro_let(Expr& expr, int& pos) const
    {

    }

    void Parser::Preprocess::parse_macro_if(Expr& expr, int& pos) const
    {
        // const int expr_size = expr.size();
        // const int if_pos = pos-1;
        // const bool cond = parse_value<int>(expr, pos);
        // int body_pos = pos;
        // int else_pos = -1;
        // int end_pos = -1;
        // const int if_size = body_pos-if_pos;

        // while (pos < expr_size) {
        //     if (!expr[pos]->is_etoken()) {
        //         pos++;
        //         continue;
        //     }
        //     Macro_key& mkey = get_token(expr, pos);
        //     if (mkey == "#endif") {
        //         end_pos = pos-1;
        //         break;
        //     }
        //     if (mkey == "#else") {
        //         else_pos = pos-1;
        //     }
        // }
        // expect(end_pos > if_pos, "#endif not found.");
        // const bool else_branch = (else_pos > if_pos);
        // const int end_size = end_pos-body_pos+1;
        // const int else_size = else_pos-body_pos+1;
        // const int end_else_size = end_pos-else_pos+1;

        // expr.erase_places(if_pos, if_size);
        // body_pos -= if_size;
        // else_pos -= if_size;
        // end_pos -= if_size;
        // if (cond) {
        //     if (else_branch) {
        //         return expr.erase_places(else_pos, end_else_size);
        //     }
        //     return expr.erase_place(end_pos);
        // }
        // if (!else_branch) {
        //     return expr.erase_places(body_pos, end_size);
        // }
        // expr.erase_place(end_pos);
        // expr.erase_places(body_pos, else_size);
    }

    void Parser::Preprocess::parse_macro_for(Expr& expr, int& pos) const
    {

    }

    template <typename Arg>
    Arg Parser::Preprocess::parse_value(Expr& expr, int& pos)
    {
        // Expr_token& literal = get_etoken_check(expr, pos);
        // if (literal.ctoken() == "$") {
        //     return get_expr_check(expr, pos).get_eval<Arg>()();
        // }
        // return literal.get_value_check<Arg>();
    }
}
