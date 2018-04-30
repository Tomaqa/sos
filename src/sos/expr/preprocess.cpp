#include "expr/preprocess.hpp"
#include "expr/eval.hpp"

namespace SOS {
    const Expr::Preprocess::Reserved_macro_fs_map
        Expr::Preprocess::reserved_macro_fs_map{
        {"#def",    &Expr::Preprocess::parse_macro_def},
        {"#let",    &Expr::Preprocess::parse_macro_let},
        {"#endlet", &Expr::Preprocess::parse_macro_endlet},
        {"#if",     &Expr::Preprocess::parse_macro_if},
        {"#for",    &Expr::Preprocess::parse_macro_for},
    };

    Expr::Preprocess::Preprocess(Expr expr)
        : _expr(move(expr))
    {
        add_macro("", {}, {});
    }

    Expr::Preprocess::Preprocess(string input)
        : Preprocess(Expr(parse_lines(move(input))))
    { }

    Expr::Preprocess::Preprocess(istream& is)
        : Preprocess(Expr(parse_lines(is)))
    { }

    Expr Expr::Preprocess::parse()
    {
        unsigned depth = 0;
        parse_nested_expr(_expr, depth);
        return move(_expr);
    }

    string Expr::Preprocess::parse_lines(string&& input)
    {
        istringstream iss(move(input));
        return parse_lines(iss);
    }

    string Expr::Preprocess::parse_lines(istream& is)
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

    bool Expr::Preprocess::is_macro_key(const Token& token)
    {
        return is_macro_key_char(token[0]);
    }

    bool Expr::Preprocess::is_macro_key_char(char c)
    {
        return c == '#';
    }

    void Expr::Preprocess::check_is_not_macro_key(const Token& token)
    {
        expect(!is_macro_key(token),
               "Specify the macro name '"s + to_string(token)
               + "' as a simple token without '#'");
    }

    bool Expr::Preprocess::is_arith_expr(const Token& token)
    {
        return is_arith_expr_char(token[0]);
    }

    bool Expr::Preprocess::is_arith_expr_char(char c)
    {
        return c == '$';
    }

    bool Expr::Preprocess::is_reserved_macro_key(const Macro_key& macro_key_)
    {
        return reserved_macro_fs_map.includes(macro_key_);
    }

    bool Expr::Preprocess::has_macro_key(const Macro_key& macro_key_) const
    {
        return cmacros_map().count(macro_key_) == 1;
    }

    void Expr::Preprocess::
        check_has_not_macro_key(const Macro_key& macro_key_) const
    {
        expect(!has_macro_key(macro_key_),
               "Macro named '"s + macro_key_ + "' "
               + "has already been defined.");
    }

    const Expr::Preprocess::Macro&
        Expr::Preprocess::cmacro(const Macro_key& macro_key_) const
    {
        return cmacros_map().at(macro_key_);
    }

    Expr::Preprocess::Macro&
        Expr::Preprocess::macro(const Macro_key& macro_key_)
    {
        return macros_map()[macro_key_];
    }

    const Expr::Preprocess::Macro_param_keys&
        Expr::Preprocess::cmacro_param_keys(const Macro_key& macro_key_) const
    {
        return std::get<0>(cmacro(macro_key_));
    }

    Expr::Preprocess::Macro_param_keys&
        Expr::Preprocess::macro_param_keys(const Macro_key& macro_key_)
    {
        return std::get<0>(macro(macro_key_));
    }

    bool Expr::Preprocess::
        macro_param_keys_has_param_key(const Macro_param_keys&
                                           macro_param_keys_,
                                       const Macro_param_key&
                                           macro_param_key_)
    {
        return includes(macro_param_keys_, macro_param_key_);
    }

    bool Expr::Preprocess::
        macro_has_param_key(const Macro_key& macro_key_,
                            const Macro_param_key& macro_param_key_) const
    {
        return macro_param_keys_has_param_key(cmacro_param_keys(macro_key_),
                                              macro_param_key_);
    }

    const Expr::Preprocess::Macro_body&
        Expr::Preprocess::cmacro_body(const Macro_key& macro_key_) const
    {
        return std::get<1>(cmacro(macro_key_));
    }

    Expr::Preprocess::Macro_body&
        Expr::Preprocess::macro_body(const Macro_key& macro_key_)
    {
        return std::get<1>(macro(macro_key_));
    }

    void Expr::Preprocess::add_macro(const Macro_key& macro_key_,
                                     Macro_param_keys macro_param_keys_,
                                     Macro_body macro_body_)
    {
        macro(macro_key_) = make_tuple(move(macro_param_keys_),
                                       move(macro_body_));
    }

    bool Expr::Preprocess::has_let_key(const Let_key& let_key_) const
    {
        return clets_map().count(let_key_) == 1 && !clet(let_key_).empty();
    }

    void Expr::Preprocess::check_has_let_key(const Let_key& let_key_) const
    {
        expect(has_let_key(let_key_),
               "Let named '"s + let_key_ + "' "
               + "is not defined within this context.");
    }

    const Expr::Preprocess::Let&
        Expr::Preprocess::clet(const Let_key& let_key_) const
    {
        return clets_map().at(let_key_);
    }

    Expr::Preprocess::Let&
        Expr::Preprocess::let(const Let_key& let_key_)
    {
        return clets_map()[let_key_];
    }

    const Expr::Preprocess::Let_body&
        Expr::Preprocess::clet_body(const Let_key& let_key_) const
    {
        return clet(let_key_).top();
    }

    Expr::Preprocess::Let_body&
        Expr::Preprocess::let_body(const Let_key& let_key_)
    {
        return let(let_key_).top();
    }

    void Expr::Preprocess::push_let_body(const Let_key& let_key_,
                                   Let_body let_body_)
    {
        let(let_key_).emplace(move(let_body_));
    }

    void Expr::Preprocess::pop_let_body(const Let_key& let_key_)
    {
        let(let_key_).pop();
    }

    void Expr::Preprocess::parse_nested_expr(Expr& expr, unsigned depth)
    try {
        while (expr) {
            if (!is_expr(expr.cpeek())) {
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

    void Expr::Preprocess::check_token(const Expr& expr,
                                       unsigned depth) const
    {
        const Token& token = expr.cpeek_token();
        token_check_token(token, depth);
    }

    void Expr::Preprocess::token_check_token(const Token& token,
                                             unsigned depth)
    {
        expect(depth > 0,
               "Unexpected token at top level: '"s
               + token + "'");
    }

    template <typename F>
    Expr::Preprocess::Exp_pos
        Expr::Preprocess::parse_and_return(Expr& expr, F f)
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

    void Expr::Preprocess::parse_token(Expr& expr, unsigned depth)
    {
        Token& token = expr.peek_token();
        Tokens tokens = split_token(token);
        if (tokens.empty()) {
            return parse_token_single(expr, token, depth);
        }
        parse_token_multi(expr, tokens, depth);
    }

    Expr::Preprocess::Exp_pos
        Expr::Preprocess::exp_token(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_token(expr, depth);
        });
    }

    void Expr::Preprocess::parse_macro(Expr& expr, unsigned depth)
    {
        Macro_key mkey = expr.extract_token();
        if (is_reserved_macro_key(mkey)) {
            parse_reserved_macro(expr, mkey, depth);
        }
        else {
            parse_user_macro(expr, mkey, depth);
        }
    }

    void Expr::Preprocess::parse_reserved_macro(Expr& expr,
                                                const Macro_key& macro_key_,
                                                unsigned depth)
    {
        expect(depth == 0 || _macro_depth > 0,
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        reserved_macro_fs_map[macro_key_](this, expr, depth);
    }

    void Expr::Preprocess::parse_macro_def(Expr& expr, unsigned depth)
    {
        Macro_key macro_key_ = expr.extract_token_check();
        check_is_not_macro_key(macro_key_);
        check_has_not_macro_key(macro_key_);
        Expr params_expr;
        if (expr && is_expr(expr.cpeek())) {
            params_expr = expr.extract_expr();
        }
        //! do not parse this expression
        Macro_param_keys macro_param_keys_ =
            params_expr.transform_to_tokens();
        Macro_body macro_body_ = extract_macro_body(expr, "def");
        add_macro(move(macro_key_), move(macro_param_keys_),
                  move(macro_body_));
    }

    void Expr::Preprocess::parse_macro_let(Expr& expr, unsigned depth)
    {
        ++_macro_depth;
        Let_key let_key_ = expr.extract_token_check();
        check_is_not_macro_key(let_key_);
        expect(expr, "Expected definition of '"s
                     + let_key_ + "' #let.");

        Let_body let_body_;

        if (!is_expr(expr.cpeek())) {
            auto it = exp_token(expr, depth+1);
            if (it == expr.cpos()) {
                expr.add_new_etoken_at_pos();
                expr.prev();
            }
        }
        if (!is_expr(expr.cpeek())) {
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

    void Expr::Preprocess::parse_macro_endlet(Expr& expr, unsigned depth)
    {
        Let_key let_key_ = expr.extract_token_check();
        check_is_not_macro_key(let_key_);
        check_has_let_key(let_key_);
        pop_let_body(let_key_);
    }

    void Expr::Preprocess::parse_macro_if(Expr& expr, unsigned depth)
    {
        const bool cond = ceval_value<bool>(
            parse_eval_arith_token(expr, depth+1)
        );
        bool del = !cond;
        bool found = false;
        int nested_del_cnt = 0;
        while (expr) {
            if (is_expr(expr.cpeek())) {
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
                if (nested_del_cnt) {
                    --nested_del_cnt;
                    continue;
                }
                found = true;
                break;
            }
            if (token == "#else") {
                expr.erase_at_pos();
                del = !del;
                continue;
            }
            if (del) {
                if (token == "#if") ++nested_del_cnt;
                expr.erase_at_pos();
                continue;
            }
            parse_token(expr, depth);
        }
        expect(found, "'#endif' not found.");
    }

    void Expr::Preprocess::parse_macro_for(Expr& expr, unsigned depth)
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

        Macro_body macro_body_ = extract_macro_body(expr, "for");

        push_let_body(var, {});
        for (For_eval_t i = init; i <= end; ++i) {
            let_body(var) = to_string(i);
            Macro_body tmp_mbody = macro_body_;
            parse_nested_expr(tmp_mbody, depth);
            move(tmp_mbody, std::inserter(expr, expr.pos()));
        }
        pop_let_body(var);
    }

    void Expr::Preprocess::parse_user_macro(Expr& expr,
                                            Macro_key& macro_key_,
                                            unsigned depth)
    {
        macro_key_.erase(0, 1);
        if (is_macro_key(macro_key_)) {
            if (macro_key_.size() == 1) {
                macro_key_.push_back(macro_key_.front());
            }
            token_check_token(macro_key_, depth);
            expr.add_new_etoken_at_pos(move(macro_key_));
            return;
        }
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

    Expr::Preprocess::Eval_t_marked
        Expr::Preprocess::parse_eval_arith_token(Expr& expr, unsigned depth)
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

    Expr::Preprocess::Eval_t_marked
        Expr::Preprocess::parse_eval_arith_expr(Expr& expr, unsigned depth)
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

    void Expr::Preprocess::parse_arith_expr(Expr& expr, unsigned depth)
    {
        const auto val_m = parse_eval_arith_expr(expr, depth);
        if (ceval_is_float(val_m))
            expr.add_new_etoken_at_pos(ceval_value<Eval_float_t>(val_m));
        else expr.add_new_etoken_at_pos(ceval_value<Eval_int_t>(val_m));
    }

    Expr::Preprocess::Exp_pos
        Expr::Preprocess::exp_arith_expr(Expr& expr, unsigned depth)
    {
        return parse_and_return(expr, [this, &expr, depth](){
            parse_arith_expr(expr, depth);
        });
    }

    void Expr::Preprocess::parse_token_single(Expr& expr,
                                              Token& token,
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

    void Expr::Preprocess::parse_token_multi(Expr& expr,
                                             Tokens& tokens,
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
                Token& token = expr.peek_token();
                parse_token_single(expr, token, depth);
            }
        });
        if (expr.pos() == eit) return;
        Token& token = expr.get_token_check();
        while (expr.pos() != eit) {
            token += expr.extract_token_check();
        }
    }

    Expr::Preprocess::Macro_body Expr::Preprocess::
        extract_macro_body(Expr& expr, Macro_key macro_key_)
    {
        Token end_token = "#end" + macro_key_;
        macro_key_ = '#' + move(macro_key_);
        Macro_body macro_body_;
        bool found = false;
        int nested_cnt = 0;
        while (expr) {
            Expr_place_ptr place = expr.extract();
            if (!is_expr(place)) {
                const Token& token = cptr_to_token(place);
                if (token == end_token) {
                    if (nested_cnt == 0) {
                        found = true;
                        break;
                    }
                    --nested_cnt;
                }
                if (token == macro_key_) {
                    ++nested_cnt;
                }
            }
            macro_body_.add_place_ptr(move(place));
        }
        expect(found, to_string(end_token) + " not found.");
        return macro_body_;
    }

    void Expr::Preprocess::
        parse_user_macro_push_params(Expr& expr,
                                     const Macro_key& macro_key_,
                                     unsigned depth)
    {
        ++_macro_depth;
        const Macro_param_keys& macro_param_keys_ =
            cmacro_param_keys(macro_key_);
        const int params_size = macro_param_keys_.size();
        const bool empty = (params_size == 0);
        if (empty && !expr) return;

        Expr params_expr;
        if (!empty) {
            expect(expr && is_expr(expr.cpeek()),
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

        Util::for_each(macro_param_keys_,
                       std::make_move_iterator(std::begin(params_expr)),
                       [this](const Macro_param_key& mparkey,
                              Expr_place_ptr&& val){
                           push_let_body(mparkey, move(val));
                       });
    }

    void Expr::Preprocess::
        parse_user_macro_pop_params(Expr& expr,
                                    const Macro_key& macro_key_)
    {
        --_macro_depth;
        const Macro_param_keys& macro_param_keys_ =
            cmacro_param_keys(macro_key_);
        for (auto& mpar : macro_param_keys_) {
            pop_let_body(mpar);
        }
    }

    Expr::Tokens Expr::Preprocess::split_token(Token& token)
    {
        Tokens tokens = inplace_split_if<Tokens>(
            token,
            [](char c){ return is_macro_key_char(c); }
        );
        if (tokens.empty()) return tokens;
        split_token_process_part(token, tokens[0]);
        if (token.empty() && tokens.size() == 1) {
            token = move(tokens[0]);
            tokens.pop_back();
            return tokens;
        }
        const int size_ = tokens.size();
        for (int i = 0; i < size_-1; i++) {
            split_token_process_part(tokens[i], tokens[i+1]);
        }
        return tokens;
    }

    void Expr::Preprocess::split_token_process_part(Token& token, Token& succ)
    {
        if (token == "#" || token == "##") {
            succ.erase(0, 1);
            return;
        }
        if (token.back() == '\\' && succ.front() == '#') {
            token.pop_back();
            succ = succ.front() + move(succ);
        }
    }

    template <typename Arg>
    Expr::Preprocess::Eval_t_marked
        Expr::Preprocess::new_eval_marked_helper(Arg val, bool is_float)
    {
        Eval_t_marked val_m;
        eval_value<Arg>(val_m) = val;
        eval_is_float(val_m) = is_float;
        return val_m;
    }

    Expr::Preprocess::Eval_t_marked
        Expr::Preprocess::new_eval_marked_float(Eval_float_t val)
    {
        return new_eval_marked_helper(val, true);
    }

    Expr::Preprocess::Eval_t_marked
        Expr::Preprocess::new_eval_marked_int(Eval_int_t val)
    {
        return new_eval_marked_helper(val, false);
    }

    Expr::Preprocess::Eval_t
        Expr::Preprocess::ceval_union(const Eval_t_marked& val_m)
    {
        return val_m.first;
    }

    Expr::Preprocess::Eval_t&
        Expr::Preprocess::eval_union(Eval_t_marked& val_m)
    {
        return val_m.first;
    }

    bool Expr::Preprocess::ceval_is_float(const Eval_t_marked& val_m)
    {
        return val_m.second;
    }

    bool& Expr::Preprocess::eval_is_float(Eval_t_marked& val_m)
    {
        return val_m.second;
    }

    template <typename Arg>
    Arg Expr::Preprocess::ceval_value(const Eval_t_marked& val_m)
    {
        if (ceval_is_float(val_m))
            return ceval_union(val_m).f;
        return ceval_union(val_m).i;
    }

    template <typename Arg>
    Arg& Expr::Preprocess::eval_value(Eval_t_marked& val_m)
    {
        if (ceval_is_float(val_m))
            return (Arg&)eval_union(val_m).f;
        return (Arg&)eval_union(val_m).i;
    }
}
