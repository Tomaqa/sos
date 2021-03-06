#include "expr.hpp"

namespace SOS {
    string to_string(const Expr_place& rhs)
    {
        return (string)rhs;
    }

    ostream& operator <<(ostream& os, const Expr_place& rhs)
    {
        return (os << to_string(rhs));
    }

    bool operator ==(const Expr_place& lhs, const Expr_place& rhs)
    {
        return to_string(lhs) == to_string(rhs);
    }

    bool operator !=(const Expr_place& lhs, const Expr_place& rhs)
    {
        return !(lhs == rhs);
    }

    ///////////////////////////////////////////////////////////////

    Expr_token::Expr_token()
        : Expr_token("")
    { }

    Expr_token::Expr_token(Token token)
        : Expr_value<Token>(move(token))
    { }

    Expr_token::Expr_token(char arg)
    {
        set_value<char>(arg);
    }

    Expr_token::Expr_token(int arg)
    {
        set_value<int>(arg);
    }

    Expr_token::Expr_token(double arg)
    {
        set_value<double>(arg);
    }

    Expr_place::Expr_place_ptr Expr_token::clone() const
    {
        return new_etoken(*this);
    }

    Expr_place::Expr_place_ptr Expr_token::move_to_ptr()
    {
        return new_etoken(move(*this));
    }

    const Expr_place::Token& Expr_token::check_token(const Token& token)
    {
        expect(valid_token(token),
               "Invalid token: "s + to_string(token));
        return token;
    }

    bool Expr_token::valid_token(const Token& token)
    {
        return !token.empty();
    }

    ///////////////////////////////////////////////////////////////

    Expr_place::Expr_place_ptr Expr::clone() const
    {
        return new_expr(*this);
    }

    Expr_place::Expr_place_ptr Expr::move_to_ptr()
    {
        return new_expr(move(*this));
    }

    Expr::Expr(const Expr& rhs)
        : _is_simplified(rhs._is_simplified),
          _is_binary(rhs._is_binary),
          _is_flatten(rhs._is_flatten)
    {
        for (const auto& e : rhs) {
            add_place_ptr(e->clone());
        }
    }

    Expr& Expr::operator =(Expr rhs)
    {
        swap(rhs);
        return *this;
    }

    void Expr::swap(Expr& rhs)
    {
        std::swap(_places, rhs._places);
        std::swap(_is_simplified, rhs._is_simplified);
        std::swap(_is_binary, rhs._is_binary);
        std::swap(_is_flatten, rhs._is_flatten);
        std::swap(_pos, rhs._pos);
        std::swap(_valid_pos, rhs._valid_pos);
    }

    Expr::Expr(initializer_list<Expr_place_ptr> list)
        : Expr()
    {
        for (const auto& e : list) {
            add_place_ptr(e->clone());
        }
    }

    Expr::Expr(Expr_place_ptr place)
        : Expr()
    {
        add_place_ptr(move(place));
    }

    Expr::Expr(string input)
        : Expr(istringstream(move(input)))
    { }

    Expr::Expr(istream& is)
        : Expr()
    {
        streampos last_pos = is.tellg();
        try {
            parse(is, last_pos, 0);
        }
        catch (const Error& err) {
            is.clear();
            auto size_ = is.tellg() - last_pos;
            if (size_ <= 0) throw;
            is.seekg(last_pos);
            string str;
            str.reserve(size_);
            for (decltype(size_) i = 0; i < size_; i++) {
                str += (char)is.get();
            }
            throw "At '"s + str
                  + "':\n" + err;
        }
        simplify_top();
    }

    Expr::Expr(istream&& is)
        : Expr(is)
    { }

    Expr::Expr(istream& is, streampos& last_pos, unsigned depth)
        : Expr()
    {
        parse(is, last_pos, depth);
    }

    void Expr::parse(istream& is, streampos& last_pos, unsigned depth)
    {
        char c;
        string str;
        ostringstream oss_buf;

        bool closed = false;
        is >> std::noskipws;
        while (is >> c) {
            if (isspace(c)) continue;
            if (!isprint(c)) {
                expect(c == 0,
                       "Unexpected non-printable character ("s
                       + to_string((int)c) + ")");
            }
            if (c == '(') {
                last_pos = is.tellg();
                add_new_expr(is, last_pos, depth+1);
                continue;
            }
            if (c == ')') {
                expect(depth > 0,
                       "Unexpected closing brace "s
                       + "in top level expression.");
                closed = true;
                break;
            }
            oss_buf << c;
            char c2 = is.peek();
            if (isspace(c2) || c2 == '(') {
                add_new_etoken(oss_buf.str());
                oss_buf.str("");
            }
        }

        expect(closed || depth == 0,
               "Closing brace at level "s
               + to_string(depth) + " not found.");

        if (!oss_buf.str().empty()) {
            add_new_etoken(oss_buf.str());
        }
    }

    Expr::operator string () const noexcept
    {
        string str("( ");
        for (const auto& e : *this) {
            str += to_string(*e) + " ";
        }
        return (str += ")");
    }

    Expr::operator bool () const
    {
        return valid_pos();
    }

    const Expr_place::Expr_place_ptr& Expr::cfront() const
    {
        return cplaces().front();
    }

    const Expr_place::Expr_place_ptr& Expr::cback() const
    {
        return cplaces().back();
    }

    Expr_place::Expr_place_ptr& Expr::front()
    {
        return places().front();
    }

    Expr_place::Expr_place_ptr& Expr::back()
    {
        return places().back();
    }

    Expr::const_iterator Expr::cpos() const
    {
        return _pos;
    }

    Expr::iterator Expr::pos()
    {
        return _pos;
    }

    Expr::iterator& Expr::rpos()
    {
        return _pos;
    }

    void Expr::set_pos(const_iterator it)
    {
        set_pos(to_iterator(it));
    }

    void Expr::set_pos(iterator it)
    {
        rpos() = it;
        _valid_pos = true;
        maybe_invalidate_pos();
    }

    Expr::iterator Expr::to_iterator(const_iterator it)
    {
        return erase(it, it);
    }

    bool Expr::valid_pos() const
    {
        if (!_valid_pos) return false;
        maybe_invalidate_pos();
        return _valid_pos;
    }

    void Expr::check_pos() const
    {
        expect(valid_pos(),
               "Unexpected end of expression.");
    }

    void Expr::reset_pos()
    {
        set_pos(begin());
    }

    void Expr::maybe_reset_pos()
    {
        if (!valid_pos()) {
            reset_pos();
        }
    }

    void Expr::invalidate_pos() const
    {
        _valid_pos = false;
    }

    void Expr::maybe_invalidate_pos() const
    {
        if (cpos() == end()) invalidate_pos();
    }

    Expr& Expr::next()
    {
        ++rpos();
        return *this;
    }

    Expr& Expr::prev()
    {
        --rpos();
        return *this;
    }

    const Expr_place::Expr_place_ptr& Expr::cpeek() const
    {
        return *cpos();
    }

    Expr_place::Expr_place_ptr& Expr::peek()
    {
        return *pos();
    }

    Expr_place::Expr_place_ptr& Expr::get()
    {
        return *rpos()++;
    }

    Expr_place::Expr_place_ptr Expr::extract()
    {
        Expr_place_ptr place = move(peek());
        erase_at_pos();
        return place;
    }

    const Expr_place::Expr_place_ptr& Expr::cpeek_check() const
    {
        check_pos();
        return cpeek();
    }

    Expr_place::Expr_place_ptr& Expr::peek_check()
    {
        check_pos();
        return peek();
    }

    Expr_place::Expr_place_ptr& Expr::get_check()
    {
        check_pos();
        return get();
    }

    Expr_place::Expr_place_ptr Expr::extract_check()
    {
        check_pos();
        return extract();
    }

    bool Expr::is_evalue(const Expr_place_ptr& place_ptr)
    {
        return !is_expr(place_ptr) && !is_etoken(place_ptr);
    }

    bool Expr::is_etoken(const Expr_place_ptr& place_ptr)
    {
        return dynamic_cast<Expr_token*>(place_ptr.get());
    }

    bool Expr::is_expr(const Expr_place_ptr& place_ptr)
    {
        return place_ptr->is_expr();
    }

    void Expr::check_is_evalue(const Expr_place_ptr& place_ptr)
    {
        expect(is_evalue(place_ptr),
               "Expected value, got: "s
               + to_string(*place_ptr));
    }

    void Expr::check_is_etoken(const Expr_place_ptr& place_ptr)
    {
        expect(is_etoken(place_ptr),
               "Expected token, got: "s
               + to_string(*place_ptr));
    }

    void Expr::check_is_expr(const Expr_place_ptr& place_ptr)
    {
        expect(is_expr(place_ptr),
               "Expected expression, got: "s
               + to_string(*place_ptr));
    }

    const Expr_token& Expr::cptr_to_etoken(const Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_token&>(*place_ptr);
    }

    const Expr::Token& Expr::cptr_to_token(const Expr_place_ptr& place_ptr)
    {
        return cptr_to_etoken(place_ptr).ctoken();
    }

    const Expr& Expr::cptr_to_expr(const Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr&>(*place_ptr);
    }

    Expr_token& Expr::ptr_to_etoken(Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_token&>(*place_ptr);
    }

    Expr::Token& Expr::ptr_to_token(Expr_place_ptr& place_ptr)
    {
        return ptr_to_etoken(place_ptr).token();
    }

    Expr& Expr::ptr_to_expr(Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr&>(*place_ptr);
    }

    const Expr_token& Expr::cto_etoken(iterator it) const
    {
        return cptr_to_etoken(*it);
    }

    const Expr::Token& Expr::cto_token(iterator it) const
    {
        return cptr_to_token(*it);
    }

    const Expr& Expr::cto_expr(iterator it) const
    {
        return cptr_to_expr(*it);
    }

    Expr_token& Expr::to_etoken(iterator it)
    {
        return ptr_to_etoken(*it);
    }

    Expr::Token& Expr::to_token(iterator it)
    {
        return ptr_to_token(*it);
    }

    Expr& Expr::to_expr(iterator it)
    {
        return ptr_to_expr(*it);
    }

    const Expr_token& Expr::cpeek_etoken() const
    {
        return cptr_to_etoken(cpeek());
    }

    const Expr::Token& Expr::cpeek_token() const
    {
        return cptr_to_token(cpeek());
    }

    const Expr& Expr::cpeek_expr() const
    {
        return cptr_to_expr(cpeek());
    }

    Expr_token& Expr::get_etoken()
    {
        return ptr_to_etoken(get());
    }

    Expr::Token& Expr::get_token()
    {
        return ptr_to_token(get());
    }

    Expr& Expr::get_expr()
    {
        return ptr_to_expr(get());
    }

    Expr_token& Expr::peek_etoken()
    {
        return ptr_to_etoken(peek());
    }

    Expr::Token& Expr::peek_token()
    {
        return ptr_to_token(peek());
    }

    Expr& Expr::peek_expr()
    {
        return ptr_to_expr(peek());
    }

    Expr_token Expr::extract_etoken()
    {
        Expr_place_ptr place = extract();
        return move(ptr_to_etoken(place));
    }

    Expr::Token Expr::extract_token()
    {
        Expr_place_ptr place = extract();
        return move(ptr_to_token(place));
    }

    Expr Expr::extract_expr()
    {
        Expr_place_ptr place = extract();
        return move(ptr_to_expr(place));
    }

    const Expr_token&
        Expr::cptr_to_etoken_check(const Expr_place_ptr& place_ptr)
    {
        check_is_etoken(place_ptr);
        return cptr_to_etoken(place_ptr);
    }

    const Expr::Token&
        Expr::cptr_to_token_check(const Expr_place_ptr& place_ptr)
    {
        check_is_etoken(place_ptr);
        return cptr_to_token(place_ptr);
    }

    const Expr& Expr::cptr_to_expr_check(const Expr_place_ptr& place_ptr)
    {
        check_is_expr(place_ptr);
        return cptr_to_expr(place_ptr);
    }

    Expr_token& Expr::ptr_to_etoken_check(Expr_place_ptr& place_ptr)
    {
        check_is_etoken(place_ptr);
        return ptr_to_etoken(place_ptr);
    }

    Expr::Token& Expr::ptr_to_token_check(Expr_place_ptr& place_ptr)
    {
        check_is_etoken(place_ptr);
        return ptr_to_token(place_ptr);
    }

    Expr& Expr::ptr_to_expr_check(Expr_place_ptr& place_ptr)
    {
        check_is_expr(place_ptr);
        return ptr_to_expr(place_ptr);
    }

    const Expr_token& Expr::cto_etoken_check(iterator it) const
    {
        return cptr_to_etoken_check(*it);
    }

    const Expr::Token& Expr::cto_token_check(iterator it) const
    {
        return cptr_to_token_check(*it);
    }

    const Expr& Expr::cto_expr_check(iterator it) const
    {
        return cptr_to_expr_check(*it);
    }

    Expr_token& Expr::to_etoken_check(iterator it)
    {
        return ptr_to_etoken_check(*it);
    }

    Expr::Token& Expr::to_token_check(iterator it)
    {
        return ptr_to_token_check(*it);
    }

    Expr& Expr::to_expr_check(iterator it)
    {
        return ptr_to_expr_check(*it);
    }

    const Expr_token& Expr::cpeek_etoken_check() const
    {
        return cptr_to_etoken_check(cpeek_check());
    }

    const Expr::Token& Expr::cpeek_token_check() const
    {
        return cptr_to_token_check(cpeek_check());
    }

    const Expr& Expr::cpeek_expr_check() const
    {
        return cptr_to_expr_check(cpeek_check());
    }

    Expr_token& Expr::get_etoken_check()
    {
        return ptr_to_etoken_check(get_check());
    }

    Expr::Token& Expr::get_token_check()
    {
        return ptr_to_token_check(get_check());
    }

    Expr& Expr::get_expr_check()
    {
        return ptr_to_expr_check(get_check());
    }

    Expr_token& Expr::peek_etoken_check()
    {
        return ptr_to_etoken_check(peek_check());
    }

    Expr::Token& Expr::peek_token_check()
    {
        return ptr_to_token_check(peek_check());
    }

    Expr& Expr::peek_expr_check()
    {
        return ptr_to_expr_check(peek_check());
    }

    Expr_token Expr::extract_etoken_check()
    {
        Expr_place_ptr place = extract_check();
        return move(ptr_to_etoken_check(place));
    }

    Expr::Token Expr::extract_token_check()
    {
        Expr_place_ptr place = extract_check();
        return move(ptr_to_token_check(place));
    }

    Expr Expr::extract_expr_check()
    {
        Expr_place_ptr place = extract_check();
        return move(ptr_to_expr_check(place));
    }

    Expr::iterator Expr::erase(const_iterator pos)
    {
        auto next_it = pos;
        return erase(pos, ++next_it);
    }

    Expr::iterator Expr::erase(const_iterator first, const_iterator last)
    {
        auto it = places().erase(first, last);
        if (first == cpos()) {
            set_pos(it);
        }
        return it;
    }

    void Expr::resize(size_t size_)
    {
        if (size_ == 0) {
            return clear();
        }
        places().resize(size_);
        reset_pos();
    }

    void Expr::clear()
    {
        places().clear();
        invalidate_pos();
    }

    void Expr::erase_at_pos()
    {
        erase(cpos());
    }

    void Expr::erase_from_pos()
    {
        erase(cpos(), end());
    }

    void Expr::erase_from_pos(const_iterator last)
    {
        erase(cpos(), last);
    }

    Expr& Expr::simplify() noexcept
    {
        if (_is_simplified) return *this;
        _is_simplified = true;
        return simplify_rec();
    }

    Expr& Expr::simplify_top() noexcept
    {
        if (size() == 1 && is_expr(cfront())) {
            Expr expr = move(to_expr(begin()));
            if (expr.empty()) {
                clear();
            }
            else {
                places() = move(expr.places());
                reset_pos();
            }
        }
        return *this;
    }

    Expr& Expr::simplify_rec() noexcept
    {
        if (empty()) return *this;
        for (auto& eptr : *this) {
            if (!is_expr(eptr)) continue;
            Expr& expr = ptr_to_expr(eptr);
            if (expr.simplify_rec().size() == 1) {
                eptr = move(expr.front());
            }
        }
        return simplify_top();
    }

    Expr& Expr::to_binary()
    {
        if (_is_binary) return *this;
        expect(size() > 1, "Expression has not at least 2 arguments.");
        expect(is_etoken(cfront()),
               "First argument of each expression should be single token.");
        _is_binary = true;
        if (size() > 3) {
            Expr subexpr{cfront()->clone()};
            auto it = begin();
            std::advance(it, 2);
            std::move(it, end(), std::back_inserter(subexpr));
            resize(3);
            *it = subexpr.to_binary().move_to_ptr();
        }
        for_each_expr([](Expr& e){ e.to_binary(); });
        return *this;
    }

    bool Expr::is_flat() const
    {
        return std::none_of(cbegin(), cend(),
                            [this](auto& place){ return is_expr(place); });
    }

    bool Expr::is_deep() const
    {
        return std::all_of(cbegin(), cend(),
                           [this](auto& place){ return is_expr(place); });
    }

    Expr& Expr::flatten()
    {
        if (_is_flatten) return *this;
        _is_flatten = true;
        Places places_;
        for (auto& e : places()) {
            if (!is_expr(e)) {
                places_.emplace_back(move(e));
                continue;
            }
            auto&& subexpr = move(ptr_to_expr(e).flatten());
            move(subexpr, std::back_inserter(places_));
        }
        places() = move(places_);
        return *this;
    }

    Expr::Tokens Expr::transform_to_tokens() const
    {
        expect(is_flat(), "Expression does not contain only tokens.");
        Tokens tokens;
        tokens.reserve(size());
        std::transform(cbegin(), cend(),
                       std::back_inserter(tokens),
                       bind(&Expr::cptr_to_token, _1));
        return tokens;
    }

    Expr::Exprs Expr::transform_to_exprs() const
    {
        expect(is_deep(), "Expression does not contain only subexpressions.");
        Exprs exprs;
        exprs.reserve(size());
        std::transform(cbegin(), cend(),
                       std::back_inserter(exprs),
                       bind(&Expr::cptr_to_expr, _1));
        return exprs;
    }

}
