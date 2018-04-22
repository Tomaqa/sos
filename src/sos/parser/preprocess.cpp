#include "parser.hpp"

#include <iostream>

namespace SOS {
    const Parser::Preprocess::Reserved_macro_fs_map
        Parser::Preprocess::reserved_macro_fs_map{
        {"#def",    &Parser::Preprocess::parse_macro_def},
        {"#let",    &Parser::Preprocess::parse_macro_let},
        {"#endlet", &Parser::Preprocess::parse_macro_endlet},
        {"#if",     &Parser::Preprocess::parse_macro_if},
        {"#for",    &Parser::Preprocess::parse_macro_for},
    };

    Parser::Preprocess::Preprocess()
    {
        add_macro("", {}, {});
    }

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
    }

    bool Parser::Preprocess::is_macro_key(const Token& token)
    {
        return is_macro_key_char(token[0]);
    }

    bool Parser::Preprocess::is_macro_key_char(char c)
    {
        return c == '#';
    }

    bool Parser::Preprocess::is_arith_expr(const Token& token)
    {
        return token == "$";
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

    void Parser::Preprocess::check_has_let_key(const Let_key& let_key_) const
    {
        expect(has_let_key(let_key_),
               "Let named '"s + let_key_ + "' "
               + "is not defined within this context.");
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
        expect(depth > 0,
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
        Token& token = expr.peek_token();
        Tokens tokens = split_token(token);
        if (tokens.empty()) {
            return parse_token_single(expr, token, depth);
        }
        parse_token_multi(expr, tokens, depth);
    }

    void Parser::Preprocess::
        parse_token_single(Expr& expr, const Token& token,
                           unsigned depth)
    {
        if (is_macro_key(token)) {
            return parse_macro(expr, depth);
        }
        if (is_arith_expr(token)) {
            exp_arith_expr<double>(expr, depth);
        }
        check_token(expr, depth);
        expr.next();
    }

    void Parser::Preprocess::
        parse_token_multi(Expr& expr, Tokens& tokens, unsigned depth)
    {
        const int size_ = tokens.size();
        auto it = expr.pos();
        expr.next();
        for (auto&& t : tokens) {
            expr.add_new_etoken_at_pos(move(t));
        }
        expr.set_pos(it);
        auto eit = parse_and_return(expr, [this, &expr, depth, size_](){
            for (int i = 0; i <= size_; i++) {
                const Token& token = expr.cpeek_token();
                parse_token_single(expr, token, depth);
            }
        });
        if (expr.pos() == eit) return;
        Token& token = expr.get_token_check();
        while (expr.pos() != eit) {
            token += expr.extract_token_check();
        }
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
        expect(depth == 0 || _macro_depth > 0,
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        reserved_macro_fs_map[macro_key_](this, expr, depth);
    }

    void Parser::Preprocess::parse_macro_def(Expr& expr, unsigned depth)
    {
        Macro_key macro_key_ = expr.extract_token_check();
        check_has_not_macro_key(macro_key_);
        Expr params_expr;
        if (expr && !expr.cpeek()->is_etoken()) {
            params_expr = expr.extract_expr();
        }
        //! do not parse this expression
        Macro_params macro_params_ = params_expr.transform_to_tokens();

        Macro_body macro_body_;
        bool found = false;
        while (expr) {
            Expr::Expr_place_ptr place = expr.extract();
            if (place->is_etoken()
                && Expr::cptr_to_token(place) == "#enddef") {
                found = true;
                break;
            }
            macro_body_.add_place_ptr(move(place));
        }
        expect(found, "#enddef not found.");

        add_macro(move(macro_key_), move(macro_params_), move(macro_body_));
    }

    void Parser::Preprocess::parse_macro_let(Expr& expr, unsigned depth)
    {
        Let_key let_key_ = expr.extract_token_check();
        expect(expr, "Expected definition of '"s
                     + let_key_ + "' #let.");

        Let_body let_body_;
        if (expr.cpeek()->is_etoken()) {
            Token token = expr.extract_token();
            let_body_.add_new_etoken(move(token));
        }
        else {
            Expr body_expr = expr.extract_expr();
            let_body_ = move(body_expr);
        }

        push_let_body(move(let_key_), move(let_body_));
    }

    void Parser::Preprocess::parse_macro_endlet(Expr& expr, unsigned depth)
    {
        Let_key let_key_ = expr.extract_token_check();
        check_has_let_key(let_key_);
        pop_let_body(let_key_);
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
        macro_key_.erase(0, 1);
        const bool has_let = has_let_key(macro_key_);
        const bool has_macro = !has_let && has_macro_key(macro_key_);
        expect(has_let || has_macro,
               "User macro was not defined: '"s
               + macro_key_ + "'");
        Macro_body macro_body_ = (has_let)
                               ? clet_body(macro_key_)
                               : cmacro_body(macro_key_) ;
        if (has_macro) {
            parse_user_macro_push_params(expr, macro_key_, depth);
        }

        parse_nested_expr(macro_body_, depth);
        move(macro_body_, std::inserter(expr, expr.pos()));

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
                           push_let_body(mpar, move(mval));
                       });
    }

    void Parser::Preprocess::
        parse_user_macro_pop_params(Expr& expr,
                                    const Macro_key& macro_key_)
    {
        --_macro_depth;
        const Macro_params& macro_params_ = cmacro_params(macro_key_);
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

    Parser::Tokens
        Parser::Preprocess::split_token(Token& token)
    {
        Tokens tokens = inplace_split_if<Tokens>(
            token,
            [](char c){ return is_macro_key_char(c); }
        );
        if (tokens.empty()) return tokens;
        if (token == "#") {
            tokens[0].erase(0, 1);
        }
        const int size_ = tokens.size();
        for (int i = 1; i < size_; i++) {
            if (tokens[i] != "#") continue;
            if (i < size_-1) {
                tokens[++i].erase(0, 1);
            }
        }
        return tokens;
    }
}
