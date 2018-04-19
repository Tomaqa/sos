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

    Expr_place::Expr_place_ptr Expr_token::clone() const
    {
        return new_etoken(*this);
    }

    Expr_token::Expr_token(Token token)
        : _token(move(token))
    { }

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

    Expr::Expr(const Expr& rhs)
        : _is_simplified(rhs._is_simplified),
          _is_binary(rhs._is_binary),
          _is_flatten(rhs._is_flatten)
    {
        places().reserve(rhs.size());
        for (const auto& e : rhs) {
            add_place_ptr(e->clone());
        }
    }

    Expr& Expr::operator =(const Expr& rhs)
    {
        Expr tmp(rhs);
        std::swap(*this, tmp);
        return *this;
    }

    Expr::Expr(initializer_list<Expr_place_ptr> list)
        : Expr()
    {
        for (const auto& e : list) {
            add_place_ptr(e->clone());
        }
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
            throw "At '("s + str
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

    const Expr_place::Expr_place_ptr& Expr::operator [](int idx) const
    {
        return cplaces()[idx];
    }

    Expr_place::Expr_place_ptr& Expr::operator [](int idx)
    {
        return places()[idx];
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

    const Expr_token& Expr::cto_etoken(int idx) const
    {
        return cptr_to_etoken((*this)[idx]);
    }

    const Expr::Token& Expr::cto_token(int idx) const
    {
        return cptr_to_token((*this)[idx]);
    }

    const Expr& Expr::cto_expr(int idx) const
    {
        return cptr_to_expr((*this)[idx]);
    }

    Expr_token& Expr::to_etoken(int idx)
    {
        return ptr_to_etoken((*this)[idx]);
    }

    Expr::Token& Expr::to_token(int idx)
    {
        return ptr_to_token((*this)[idx]);
    }

    Expr& Expr::to_expr(int idx)
    {
        return ptr_to_expr((*this)[idx]);
    }

    void Expr::check_is_etoken(const Expr_place_ptr& place_ptr)
    {
        expect(place_ptr->is_etoken(),
               "Expected token, got: "s
               + to_string(*place_ptr));
    }

    void Expr::check_is_expr(const Expr_place_ptr& place_ptr)
    {
        expect(!place_ptr->is_etoken(),
               "Expected expression, got: "s
               + to_string(*place_ptr));
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

    const Expr_token& Expr::cto_etoken_check(int idx) const
    {
        return cptr_to_etoken_check((*this)[idx]);
    }

    const Expr::Token& Expr::cto_token_check(int idx) const
    {
        return cptr_to_token_check((*this)[idx]);
    }

    const Expr& Expr::cto_expr_check(int idx) const
    {
        return cptr_to_expr_check((*this)[idx]);
    }

    Expr_token& Expr::to_etoken_check(int idx)
    {
        return ptr_to_etoken_check((*this)[idx]);
    }

    Expr::Token& Expr::to_token_check(int idx)
    {
        return ptr_to_token_check((*this)[idx]);
    }

    Expr& Expr::to_expr_check(int idx)
    {
        return ptr_to_expr_check((*this)[idx]);
    }

    void Expr::erase_place(int idx_)
    {
        erase_places(idx_, 1);
    }

    void Expr::erase_places(int idx_, int count_)
    {
        if (count_ <= 0) {
            count_ = size() - idx_;
        }
        places().erase(begin()+idx_, begin()+idx_+count_);
    }

    Expr& Expr::simplify() noexcept
    {
        if (_is_simplified) return *this;
        _is_simplified = true;
        return simplify_rec();
    }

    Expr& Expr::simplify_top() noexcept
    {
        if (size() == 1 && !cfront()->is_etoken()) {
            places() = move(to_expr(0).places());
        }
        return *this;
    }

    Expr& Expr::simplify_rec() noexcept
    {
        if (empty()) return *this;
        for (auto& e : *this) {
            if (e->is_etoken()) continue;
            auto& e_cast = ptr_to_expr(e);
            if (e_cast.simplify_rec().size() == 1) {
                e = move(e_cast.front());
            }
        }
        return simplify_top();
    }

    Expr& Expr::to_binary()
    {
        if (_is_binary) return *this;
        expect(size() > 1, "Expression has not at least 2 arguments.");
        expect(cfront()->is_etoken(),
               "First argument of each expression should be single token.");
        _is_binary = true;
        if (size() > 3) {
            Expr subexpr{cfront()->clone()};
            for (auto&& it = begin()+2, eit = end(); it != eit; ++it) {
                subexpr.add_place_ptr(move(*it));
            }
            places().erase(begin()+3, end());
            places()[2] = new_expr(move(subexpr.to_binary()));
        }
        for_each_expr([](Expr& e){ e.to_binary(); });
        return *this;
    }

    bool Expr::is_flat() const
    {
        return std::all_of(cbegin(), cend(),
                           bind(&Expr_place::is_etoken, _1));
    }

    bool Expr::is_deep() const
    {
        return std::none_of(cbegin(), cend(),
                            bind(&Expr_place::is_etoken, _1));
    }

    Expr& Expr::flatten()
    {
        if (_is_flatten) return *this;
        _is_flatten = true;
        Places places_;
        places_.reserve(size()*2);
        for (auto& e : places()) {
            if (e->is_etoken()) {
                places_.emplace_back(move(e));
                continue;
            }
            auto&& subexpr = move(ptr_to_expr(e).flatten());
            move(subexpr.begin(), subexpr.end(), std::back_inserter(places_));
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
