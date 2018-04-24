#include "preprocess.hpp"
#include "expr/eval.hpp"

#include <iostream>

namespace SOS {
    const Preprocess::Reserved_macro_fs_map
        Preprocess::reserved_macro_fs_map{
        {"#def",    &Preprocess::parse_macro_def},
        {"#let",    &Preprocess::parse_macro_let},
        {"#endlet", &Preprocess::parse_macro_endlet},
        {"#if",     &Preprocess::parse_macro_if},
        {"#for",    &Preprocess::parse_macro_for},
    };

    Preprocess::Preprocess()
    {
        add_macro("", {}, {});
    }

    string Preprocess::parse_input(string&& input)
    {
        istringstream iss(move(input));
        return parse_input(iss);
    }

    string Preprocess::parse_input(istream& is)
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

    void Preprocess::parse_expr(Expr& expr)
    {
        unsigned depth = 0;
        parse_nested_expr(expr, depth);
    }

    bool Preprocess::is_macro_key(const Token& token)
    {
        return is_macro_key_char(token[0]);
    }

    bool Preprocess::is_macro_key_char(char c)
    {
        return c == '#';
    }

    void Preprocess::check_is_not_macro_key(const Token& token)
    {
        expect(!is_macro_key(token),
               "Specify the macro name '"s + to_string(token)
               + "' as a simple token without '#'");
    }

    bool Preprocess::is_arith_expr(const Token& token)
    {
        return is_arith_expr_char(token[0]);
    }

    bool Preprocess::is_arith_expr_char(char c)
    {
        return c == '$';
    }

    bool Preprocess::is_reserved_macro_key(const Macro_key& macro_key_)
    {
        return reserved_macro_fs_map.includes(macro_key_);
    }

    bool Preprocess::has_macro_key(const Macro_key& macro_key_) const
    {
        return cmacros_map().count(macro_key_) == 1;
    }

    void Preprocess::
        check_has_not_macro_key(const Macro_key& macro_key_) const
    {
        expect(!has_macro_key(macro_key_),
               "Macro named '"s + macro_key_ + "' "
               + "has already been defined.");
    }

    const Preprocess::Macro&
        Preprocess::cmacro(const Macro_key& macro_key_) const
    {
        return cmacros_map().at(macro_key_);
    }

    Preprocess::Macro&
        Preprocess::macro(const Macro_key& macro_key_)
    {
        return macros_map()[macro_key_];
    }

    const Preprocess::Macro_params&
        Preprocess::cmacro_params(const Macro_key& macro_key_) const
    {
        return get<0>(cmacro(macro_key_));
    }

    Preprocess::Macro_params&
        Preprocess::macro_params(const Macro_key& macro_key_)
    {
        return get<0>(macro(macro_key_));
    }

    bool Preprocess::
        macro_params_has_param(const Macro_params& macro_params_,
                               const Macro_param& macro_param_)
    {
        return includes(macro_params_, macro_param_);
    }

    bool Preprocess::macro_has_param(const Macro_key& macro_key_,
                                     const Macro_param& macro_param_) const
    {
        return macro_params_has_param(cmacro_params(macro_key_),
                                      macro_param_);
    }

    const Preprocess::Macro_body&
        Preprocess::cmacro_body(const Macro_key& macro_key_) const
    {
        return get<1>(cmacro(macro_key_));
    }

    Preprocess::Macro_body&
        Preprocess::macro_body(const Macro_key& macro_key_)
    {
        return get<1>(macro(macro_key_));
    }

    void Preprocess::add_macro(const Macro_key& macro_key_,
                               Macro_params macro_params_,
                               Macro_body macro_body_)
    {
        macro(macro_key_) = make_tuple(move(macro_params_),
                                       move(macro_body_));
    }

    bool Preprocess::has_let_key(const Let_key& let_key_) const
    {
        return clets_map().count(let_key_) == 1 && !clet(let_key_).empty();
    }

    void Preprocess::check_has_let_key(const Let_key& let_key_) const
    {
        expect(has_let_key(let_key_),
               "Let named '"s + let_key_ + "' "
               + "is not defined within this context.");
    }

    const Preprocess::Let&
        Preprocess::clet(const Let_key& let_key_) const
    {
        return clets_map().at(let_key_);
    }

    Preprocess::Let&
        Preprocess::let(const Let_key& let_key_)
    {
        return clets_map()[let_key_];
    }

    const Preprocess::Let_body&
        Preprocess::clet_body(const Let_key& let_key_) const
    {
        return clet(let_key_).top();
    }

    Preprocess::Let_body&
        Preprocess::let_body(const Let_key& let_key_)
    {
        return let(let_key_).top();
    }

    void Preprocess::push_let_body(const Let_key& let_key_,
                                   Let_body let_body_)
    {
        let(let_key_).emplace(move(let_body_));
    }

    void Preprocess::pop_let_body(const Let_key& let_key_)
    {
        let(let_key_).pop();
    }

    void Preprocess::parse_nested_expr(Expr& expr, unsigned depth)
    try {
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
    catch (const Error& err) {
        if (depth == 0) throw;
        throw "At level "s + to_string(depth)
              + ", '" + to_string(expr) + "':\n" + err;
    }

    void Preprocess::check_token(const Expr& expr,
                                 unsigned depth) const
    {
        const Token& token = expr.cpeek_token();
        expect(depth > 0,
               "Unexpected token at top level: '"s
               + token + "'");
    }

    template <typename F>
    Preprocess::Exp_pos Preprocess::parse_and_return(Expr& expr, F f)
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

    void Preprocess::parse_token(Expr& expr, unsigned depth)
    {
        Token& token = expr.peek_token();
        Tokens tokens = split_token(token);
        if (tokens.empty()) {
            return parse_token_single(expr, token, depth);
        }
        parse_token_multi(expr, tokens, depth);
    }

    Preprocess::Exp_pos
        Preprocess::exp_token(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_token(expr, depth);
        });
    }

    void Preprocess::parse_macro(Expr& expr, unsigned depth)
    {
        Macro_key mkey = expr.extract_token();
        if (is_reserved_macro_key(mkey)) {
            parse_reserved_macro(expr, mkey, depth);
        }
        else {
            parse_user_macro(expr, mkey, depth);
        }
    }

    void Preprocess::parse_reserved_macro(Expr& expr,
                                          const Macro_key& macro_key_,
                                          unsigned depth)
    {
        expect(depth == 0 || _macro_depth > 0,
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        reserved_macro_fs_map[macro_key_](this, expr, depth);
    }

    void Preprocess::parse_macro_def(Expr& expr, unsigned depth)
    {
        Macro_key macro_key_ = expr.extract_token_check();
        check_is_not_macro_key(macro_key_);
        check_has_not_macro_key(macro_key_);
        Expr params_expr;
        if (expr && !expr.cpeek()->is_etoken()) {
            params_expr = expr.extract_expr();
        }
        //! do not parse this expression
        Macro_params macro_params_ = params_expr.transform_to_tokens();
        Macro_body macro_body_ = extract_macro_body(expr, "enddef");
        add_macro(move(macro_key_), move(macro_params_), move(macro_body_));
    }

    void Preprocess::parse_macro_let(Expr& expr, unsigned depth)
    {
        ++_macro_depth;
        Let_key let_key_ = expr.extract_token_check();
        check_is_not_macro_key(let_key_);
        expect(expr, "Expected definition of '"s
                     + let_key_ + "' #let.");

        Let_body let_body_;

        if (expr.cpeek()->is_etoken()) {
            auto it = exp_token(expr, depth+1);
            if (it == expr.cpos()) {
                expr.add_new_etoken_at_pos("");
                expr.prev();
            }
        }
        if (expr.cpeek()->is_etoken()) {
            Token token = expr.extract_token();
            let_body_.add_new_etoken(move(token));
        }
        else {
            Expr body_expr = expr.extract_expr();
            parse_nested_expr(body_expr, depth+1);
            let_body_ = move(body_expr);
        }

        push_let_body(move(let_key_), move(let_body_));
        --_macro_depth;
    }

    void Preprocess::parse_macro_endlet(Expr& expr, unsigned depth)
    {
        Let_key let_key_ = expr.extract_token_check();
        check_is_not_macro_key(let_key_);
        check_has_let_key(let_key_);
        pop_let_body(let_key_);
    }

    void Preprocess::parse_macro_if(Expr& expr, unsigned depth)
    {
        const bool cond = ceval_value<bool>(
            parse_eval_arith_token(expr, depth+1)
        );
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

    void Preprocess::parse_macro_for(Expr& expr, unsigned depth)
    {
        Expr params_expr = expr.extract_expr_check();
        Macro_key var = params_expr.extract_token_check();
        const For_eval_t init = ceval_value<For_eval_t>(
            parse_eval_arith_token(params_expr, depth+1)
        );
        const For_eval_t end = ceval_value<For_eval_t>(
            parse_eval_arith_token(params_expr, depth+1)
        );
        expect(!params_expr,
               "Additional arguments of macro '#for': "s
               + to_string(params_expr));

        Macro_body macro_body_ = extract_macro_body(expr, "endfor");

        push_let_body(var, {});
        for (For_eval_t i = init; i <= end; ++i) {
            let_body(var) = to_string(i);
            Macro_body tmp_mbody = macro_body_;
            parse_nested_expr(tmp_mbody, depth);
            move(tmp_mbody, std::inserter(expr, expr.pos()));
        }
        pop_let_body(var);
    }

    void Preprocess::parse_user_macro(Expr& expr,
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

    Preprocess::Eval_t_marked
        Preprocess::parse_eval_arith_token(Expr& expr, unsigned depth)
    {
        exp_token(expr, depth);
        const Expr_token& literal = expr.cpeek_etoken_check();
        if (!is_arith_expr(literal.ctoken())) {
            const Eval_float_t ret = literal.get_value_check<Eval_float_t>();
            expr.erase_at_pos();
            return new_eval_marked_float(ret);
        }
        return parse_eval_arith_expr(expr, depth);
    }

    Preprocess::Eval_t_marked
        Preprocess::parse_eval_arith_expr(Expr& expr, unsigned depth)
    {
        Token token = expr.extract_token();
        const char arith_char = token[0];
        token.erase(0, 1);

        bool valid_arith_token = false;
        bool is_float = true;
        if (token.empty()) valid_arith_token = true;
        else {
            if (token.size() == 1) {
                valid_arith_token = true;
                switch (token[0]) {
                default:
                    valid_arith_token = false;
                    break;
                case 'd': case 'i':
                    is_float = false;
                    break;
                case 'f':
                    break;
                }
            }
        }
        expect(valid_arith_token,
               "Invalid arithmetic expansion token: '"s
               + arith_char + to_string(token) + "'");

        Expr arith_expr = expr.extract_expr_check();
        parse_nested_expr(arith_expr, depth+1);

        if (is_float)
            return new_eval_marked_float(
                arith_expr.get_eval<Eval_float_t>()()
            );
        return new_eval_marked_int(arith_expr.get_eval<Eval_int_t>()());
    }

    void Preprocess::parse_arith_expr(Expr& expr, unsigned depth)
    {
        const auto val_m = parse_eval_arith_expr(expr, depth);
        if (ceval_is_float(val_m))
            expr.add_new_etoken_at_pos(ceval_value<Eval_float_t>(val_m));
        else expr.add_new_etoken_at_pos(ceval_value<Eval_int_t>(val_m));
    }

    Preprocess::Exp_pos
        Preprocess::exp_arith_expr(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_arith_expr(expr, depth);
        });
    }

    void Preprocess::parse_token_single(Expr& expr, const Token& token,
                                        unsigned depth)
    {
        if (is_macro_key(token)) {
            return parse_macro(expr, depth);
        }
        if (is_arith_expr(token)) {
            exp_arith_expr(expr, depth);
        }
        check_token(expr, depth);
        expr.next();
    }

    void Preprocess::parse_token_multi(Expr& expr, Tokens& tokens,
                                       unsigned depth)
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

    Preprocess::Macro_body Preprocess::
        extract_macro_body(Expr& expr, Token end_token)
    {
        end_token = "#"s + move(end_token);
        Macro_body macro_body_;
        bool found = false;
        while (expr) {
            Expr::Expr_place_ptr place = expr.extract();
            if (place->is_etoken()
                && Expr::cptr_to_token(place) == end_token) {
                found = true;
                break;
            }
            macro_body_.add_place_ptr(move(place));
        }
        expect(found, to_string(end_token) + " not found.");
        return macro_body_;
    }

    void Preprocess::
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
            parse_nested_expr(params_expr, depth+1);
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

    void Preprocess::
        parse_user_macro_pop_params(Expr& expr,
                                    const Macro_key& macro_key_)
    {
        --_macro_depth;
        const Macro_params& macro_params_ = cmacro_params(macro_key_);
        for (auto& mpar : macro_params_) {
            pop_let_body(mpar);
        }
    }

    Preprocess::Tokens Preprocess::split_token(Token& token)
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
        for (int i = 0; i < size_; i++) {
            if (tokens[i] != "#") continue;
            if (i < size_-1) {
                tokens[++i].erase(0, 1);
            }
        }
        return tokens;
    }

    template <typename Arg>
    Preprocess::Eval_t_marked
        Preprocess::new_eval_marked_helper(Arg val, bool is_float)
    {
        Eval_t_marked val_m;
        eval_value<Arg>(val_m) = val;
        eval_is_float(val_m) = is_float;
        return val_m;
    }

    Preprocess::Eval_t_marked
        Preprocess::new_eval_marked_float(Eval_float_t val)
    {
        return new_eval_marked_helper(val, true);
    }

    Preprocess::Eval_t_marked
        Preprocess::new_eval_marked_int(Eval_int_t val)
    {
        return new_eval_marked_helper(val, false);
    }

    Preprocess::Eval_t
        Preprocess::ceval_union(const Eval_t_marked& val_m)
    {
        return val_m.first;
    }

    Preprocess::Eval_t&
        Preprocess::eval_union(Eval_t_marked& val_m)
    {
        return val_m.first;
    }

    bool Preprocess::ceval_is_float(const Eval_t_marked& val_m)
    {
        return val_m.second;
    }

    bool& Preprocess::eval_is_float(Eval_t_marked& val_m)
    {
        return val_m.second;
    }

    template <typename Arg>
    Arg Preprocess::ceval_value(const Eval_t_marked& val_m)
    {
        if (ceval_is_float(val_m))
            return ceval_union(val_m).f;
        return ceval_union(val_m).i;
    }

    template <typename Arg>
    Arg& Preprocess::eval_value(Eval_t_marked& val_m)
    {
        if (ceval_is_float(val_m))
            return (Arg&)eval_union(val_m).f;
        return (Arg&)eval_union(val_m).i;
    }
}
