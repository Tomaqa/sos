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

    bool Parser::Preprocess::is_arith_expr(const Token& token)
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

    bool Parser::Preprocess::
        macro_params_has_param(const Macro_params& macro_params_,
                               const Macro_param& macro_param_)
    {
        return includes(macro_params_, macro_param_);
    }

    bool Parser::Preprocess::
        macro_has_param(const Macro_key& macro_key_,
                        const Macro_param& macro_param_) const
    {
        return macro_params_has_param(cmacro_params(macro_key_),
                                      macro_param_);
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

    bool Parser::Preprocess::has_let_key(const Let_key& let_key_) const
    {
        return clets_map().count(let_key_) == 1 && !clet(let_key_).empty();
    }

    const Parser::Preprocess::Let&
        Parser::Preprocess::clet(const Let_key& let_key_) const
    {
        return clets_map().at(let_key_);
    }

    Parser::Preprocess::Let&
        Parser::Preprocess::let(const Let_key& let_key_)
    {
        return clets_map()[let_key_];
    }

    const Parser::Preprocess::Let_body&
        Parser::Preprocess::clet_body(const Let_key& let_key_) const
    {
        return clet(let_key_).top();
    }

    Parser::Preprocess::Let_body&
        Parser::Preprocess::let_body(const Let_key& let_key_)
    {
        return let(let_key_).top();
    }

    void Parser::Preprocess::push_let_body(const Let_key& let_key_,
                                          Let_body let_body_)
    {
        let(let_key_).emplace(move(let_body_));
    }

    void Parser::Preprocess::pop_let_body(const Let_key& let_key_)
    {
        let(let_key_).pop();
    }

    // bool Parser::Preprocess::has_macro_params_l() const
    // {
    //     return !cmacro_params_ls().empty();
    // }

    // Parser::Preprocess::Macro_params_link
    //     Parser::Preprocess::macro_params_l() const
    // {
    //     return cmacro_params_ls().top();
    // }

    // bool Parser::Preprocess::
    //     macro_params_l_has_param(const Macro_param& macro_param_) const
    // {
    //     return macro_params_has_param(*macro_params_l(), macro_param_);
    // }

    // void Parser::Preprocess::
    //     push_macro_params_l(const Macro_params& macro_params_)
    // {
    //     macro_params_ls().push(&macro_params_);
    // }

    // void Parser::Preprocess::pop_macro_params_l()
    // {
    //     macro_params_ls().pop();
    // }

    void Parser::Preprocess::parse_nested_expr(Expr& expr, unsigned depth)
    {
        while (expr) {
            if (expr.cpeek()->is_etoken()) {
                parse_token(expr, depth);
                continue;
            }
            Expr& subexpr = expr.get_expr();
            parse_nested_expr(subexpr, depth+1);
        }
        expr.reset_pos_to_valid();
    }

    void Parser::Preprocess::check_token(const Expr& expr,
                                         unsigned depth) const
    {
        const Token& token = expr.cpeek_token();
        // expect(depth > 0,
        expect(depth > 0 || _macro_depth > 0,
               "Unexpected token at top level: '"s
               + token + "'");
    }

    template <typename F>
    Parser::Preprocess::Exp_pos
        Parser::Preprocess::parse_and_return(Expr& expr, F f)
    {
        auto it = expr.pos();
        const bool was_begin = (it == expr.cbegin());
        if (!was_begin) --it;
        f();
        auto end_pos = expr.pos();
        if (was_begin) expr.reset_pos();
        else expr.set_pos(++it);
        return end_pos;
    }

    void Parser::Preprocess::parse_token(Expr& expr, unsigned depth)
    {
        const Token& token = expr.cpeek_token();
        if (is_macro_key(token)) {
            return parse_macro(expr, depth);
        }
        if (is_arith_expr(token)) {
            exp_arith_expr<double>(expr, depth);
        }
        check_token(expr, depth);
        expr.next();
    }

    Parser::Preprocess::Exp_pos
        Parser::Preprocess::exp_token(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_token(expr, depth);
        });
    }

    void Parser::Preprocess::parse_macro(Expr& expr, unsigned depth)
    {
        Macro_key mkey = expr.extract_token();
        if (is_reserved_macro_key(mkey)) {
            parse_reserved_macro(expr, mkey, depth);
        }
        else {
            parse_user_macro(expr, mkey, depth);
        }
    }

    void Parser::Preprocess::
        parse_reserved_macro(Expr& expr, const Macro_key& macro_key_,
                             unsigned depth)
    {
        // expect(depth == 0,
        expect(depth == 0 || _macro_depth > 0,
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        reserved_macro_fs_map[macro_key_](this, expr, depth);
    }

    void Parser::Preprocess::parse_macro_def(Expr& expr, unsigned depth)
    {
        // expect(_macro_depth == 0,
        //        "Nested '#def' macros are not allowed.");
        // ++_macro_depth;
        Macro_key macro_key_ = expr.extract_token_check();
        // Macro_key macro_key_ = "#"s + expr.extract_token_check();
        check_has_not_macro_key(macro_key_);
        Expr params_expr;
        if (expr && !expr.cpeek()->is_etoken()) {
            params_expr = expr.extract_expr();
        }
        Macro_params macro_params_ = params_expr.transform_to_tokens();
        // for (auto& mp : macro_params_) {
        //     push_let_body("#"s+mp, "#"s+mp+"()");
        // }
        // for (auto& mp : macro_params_) {
        //     std::cout << "#"s+mp << " : " << clet_body("#"s+mp) << std::endl;
        // }
        // push_macro_params_l(macro_params_);

        Macro_body macro_body_;
        bool found = false;
        while (expr) {
            if (!expr.cpeek()->is_etoken()) {
                Expr subexpr = expr.extract_expr();
                // parse_nested_expr(subexpr, depth+1);
                macro_body_.add_new_expr(move(subexpr));
                continue;
            }
            // const Token& token = expr.cpeek_token();
            Token token = expr.extract_token();
            if (token == "#enddef") {
                // expr.erase_at_pos();
                found = true;
                break;
            }
            // Exp_pos end_pos = exp_token(expr, depth);
            // std::move(expr.pos(), end_pos,
            //           std::back_inserter(macro_body_));
            // expr.erase_from_pos(end_pos);
            macro_body_.add_new_etoken(move(token));
        }
        expect(found, "#enddef not found.");

        add_macro(move(macro_key_), move(macro_params_), move(macro_body_));
        // for (auto& mp : macro_params_) {
        //     pop_let_body(mp);
        // }
        // --_macro_depth;
        // pop_macro_params_l();
    }

    void Parser::Preprocess::parse_macro_let(Expr& expr, unsigned depth)
    {

    }

    void Parser::Preprocess::parse_macro_if(Expr& expr, unsigned depth)
    {
        const bool cond = parse_eval_token<double>(expr, depth);
        bool del = !cond;
        while (expr) {
            if (!expr.cpeek()->is_etoken()) {
                if (del) {
                    expr.erase_at_pos();
                    continue;
                }
                Expr& subexpr = expr.get_expr();
                parse_nested_expr(subexpr, depth+1);
                continue;
            }
            const Token& token = expr.cpeek_token();
            if (token == "#endif") {
                expr.erase_at_pos();
                break;
            }
            if (token == "#else") {
                expr.erase_at_pos();
                del = !del;
                continue;
            }
            if (del) {
                expr.erase_at_pos();
                continue;
            }
            parse_token(expr, depth);
        }
    }

    void Parser::Preprocess::parse_macro_for(Expr& expr, unsigned depth)
    {

    }

    void Parser::Preprocess::parse_user_macro(Expr& expr,
                                              Macro_key& macro_key_,
                                              unsigned depth)
    {
        macro_key_.erase(macro_key_.begin());
        // if (macro_params_l_has_param(macro_key_)) {
        //     if (expr && !expr.cpeek()->is_etoken()) {
        //         expr.next();
        //     }
        //     // !!!
        //     return;
        // }
        const bool has_let = has_let_key(macro_key_);
        const bool has_macro = !has_let && has_macro_key(macro_key_);
        expect(has_let || has_macro,
               "User macro was not defined: '"s
               + macro_key_ + "'");
        Macro_body macro_body_ = (has_let)
                               ? clet_body(macro_key_)
                               : cmacro_body(macro_key_) ;
        // std::cout << macro_key_ << " -> " << macro_body_ << std::endl;
        if (has_macro) {
            parse_user_macro_push_params(expr, macro_key_, depth);
        }
        // std::cout << macro_key_ << " ->* " << macro_body_ << std::endl;

        parse_nested_expr(macro_body_, depth);
        move(move(macro_body_), std::inserter(expr, expr.pos()));

        if (has_macro) {
            parse_user_macro_pop_params(expr, macro_key_);
        }
    }

    void Parser::Preprocess::
        parse_user_macro_push_params(Expr& expr,
                                     const Macro_key& macro_key_,
                                     unsigned depth)
    {
        ++_macro_depth;
        const Macro_params& macro_params_ = cmacro_params(macro_key_);
        const int params_size = macro_params_.size();
        const bool empty = (params_size == 0);
        if (empty && !expr) return;
        Expr params_expr;
        if (!empty) {
            expect(expr && !expr.cpeek()->is_etoken(),
                   "Missing parameters of user macro '"s
                   + macro_key_ + "'");
            params_expr = expr.extract_expr();
            parse_nested_expr(params_expr, depth);
            const int pexpr_size = params_expr.size();
            expect(pexpr_size == params_size,
                   "Number of user macro '"s + macro_key_
                   + "' parameters mismatch: "
                   + to_string(pexpr_size) + " != "
                   + to_string(params_size));
        }
        if (empty) return;
        Macro_params ptokens = params_expr.transform_to_tokens();
        Util::for_each(macro_params_,
                       std::make_move_iterator(std::begin(ptokens)),
                       [this](const Macro_param& mpar, Macro_param&& mval){
                           std::cout << "++" << mpar << " -> " << mval << std::endl;
                           push_let_body(mpar, move(mval));
                       });
    }

    void Parser::Preprocess::
        parse_user_macro_pop_params(Expr& expr,
                                    const Macro_key& macro_key_)
    {
        --_macro_depth;
        const Macro_params& macro_params_ = cmacro_params(macro_key_);
        if (macro_params_.empty()) return;
        for (auto& mpar : macro_params_) {
            pop_let_body(mpar);
        }
    }

    template <typename Arg>
    Arg Parser::Preprocess::parse_eval_token(Expr& expr, unsigned depth)
    {
        Expr_token literal = expr.extract_etoken_check();
        if (!is_arith_expr(literal.ctoken())) {
            return literal.get_value_check<Arg>();
        }
        return parse_eval_expr<Arg>(expr, depth);
    }

    template <typename Arg>
    Arg Parser::Preprocess::parse_eval_expr(Expr& expr, unsigned depth)
    {
        Expr arith_expr = expr.extract_expr_check();
        parse_nested_expr(arith_expr, depth+1);
        return arith_expr.get_eval<Arg>()();
    }

    template <typename Arg>
    void Parser::Preprocess::parse_arith_expr(Expr& expr, unsigned depth)
    {
        expr.erase_at_pos();
        Arg arg = parse_eval_expr<Arg>(expr, depth);
        expr.add_new_etoken_at_pos(arg);
    }

    template <typename Arg>
    Parser::Preprocess::Exp_pos
        Parser::Preprocess::exp_arith_expr(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_arith_expr<Arg>(expr, depth);
        });
    }
}
