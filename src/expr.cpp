#include "expr.hpp"

namespace SOS {
    string to_string(const Expr_place& rhs)
    {
        return move((string)rhs);
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

    Expr_place::Expr_place_ptr Expr_token::clone() const
    {
        return new_place(Expr_token(*this));
    }

    Expr_place::Expr_place_ptr Expr::clone() const
    {
        return new_place(Expr(*this));
    }

    Expr::Expr(const Expr& rhs)
        : _is_simplified(rhs._is_simplified),
          _is_binary(rhs._is_binary),
          _is_flatten(rhs._is_flatten)
    {
        _places.reserve(rhs.size());
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

    Expr::Expr(istringstream& iss, unsigned depth)
        : Expr()
    {
        char c;
        string str;
        ostringstream oss;
        bool closed = false;
        iss >> std::noskipws;
        while (iss >> c) {
            if (!isprint(c)) {
                expect(c == 0,
                       "Unexpected non-printable character ("s
                       + to_string((int)c) + ")");
            }
            if (isspace(c)) continue;
            if (c == '(') {
                add_new_place(Expr(iss, depth+1));
                continue;
            }
            if (c == ')') {
                if (depth > 0) {
                    closed = true;
                    break;
                }
                expect(depth > 0,
                       "Unexpected closing brace in top level expression.");
                closed = true;
                break;
            }
            oss << c;
            char c2 = iss.peek();
            if (isspace(c2) || c2 == '(') {
                add_new_place(Expr_token(oss.str()));
                oss.str("");
            }
        }

        expect(closed || depth == 0,
               "Closing brace at level "s + to_string(depth) + " not found.");

        if (!oss.str().empty()) {
            add_new_place(Expr_token(oss.str()));
        }

        if (depth == 0) simplify_top();
    }

    Expr::Expr(initializer_list<Expr_place_ptr> list)
        : Expr()
    {
        for (const auto& e : list) {
            add_place_ptr(e->clone());
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
        return _places[idx];
    }

    Expr_place::Expr_place_ptr& Expr::operator [](int idx)
    {
        return _places[idx];
    }

    const Expr_place::Expr_place_ptr& Expr::cfront() const
    {
        return _places.front();
    }

    const Expr_place::Expr_place_ptr& Expr::cback() const
    {
        return _places.back();
    }

    Expr_place::Expr_place_ptr& Expr::front()
    {
        return _places.front();
    }

    Expr_place::Expr_place_ptr& Expr::back()
    {
        return _places.back();
    }

    const Expr_token& Expr::cptr_to_token(const Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_token&>(*place_ptr);
    }

    const Expr& Expr::cptr_to_expr(const Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr&>(*place_ptr);
    }

    Expr_token& Expr::ptr_to_token(Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_token&>(*place_ptr);
    }

    Expr& Expr::ptr_to_expr(Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr&>(*place_ptr);
    }

    const Expr_token& Expr::cto_token(int idx) const
    {
        return cptr_to_token((*this)[idx]);
    }

    const Expr& Expr::cto_expr(int idx) const
    {
        return cptr_to_expr((*this)[idx]);
    }

    Expr_token& Expr::to_token(int idx)
    {
        return ptr_to_token((*this)[idx]);
    }

    Expr& Expr::to_expr(int idx)
    {
        return ptr_to_expr((*this)[idx]);
    }

    Expr& Expr::simplify() noexcept
    {
        if (_is_simplified) return *this;
        _is_simplified = true;
        return simplify_rec();
    }

    Expr& Expr::simplify_top() noexcept
    {
        if (size() == 1 && !cfront()->is_token()) {
            _places = move(to_expr(0)._places);
        }
        return *this;
    }

    Expr& Expr::simplify_rec() noexcept
    {
        if (empty()) return *this;
        for (auto& e : *this) {
            if (e->is_token()) continue;
            auto& e_cast = ptr_to_expr(e);
            if (e_cast.simplify_rec().size() == 1) {
                e = move(e_cast.front());
            }
        }
        return simplify_top();
    }

    Expr& Expr::to_binary(const Token& neutral)
    {
        if (_is_binary) return *this;
        expect(size() > 1, "Expression has not at least 2 arguments.");
        expect(cfront()->is_token(),
               "First argument of each expression should be single token.");
        _is_binary = true;
        if (size() == 2) {
            add_new_place(Expr_token(neutral));
            std::swap(_places[1], _places[2]);
        }
        else if (size() > 3) {
            Expr subexpr{cfront()->clone()};
            for (auto&& it = begin()+2, eit = end(); it != eit; ++it) {
                subexpr.add_place_ptr(move(*it));
            }
            _places.erase(begin()+3, end());
            _places[2] = new_place(move(subexpr.to_binary()));
        }
        for (auto& e : *this) {
            if (e->is_token()) continue;
            ptr_to_expr(e).to_binary();
        }
        return *this;
    }

    bool Expr::is_flat() const
    {
        return std::all_of(cbegin(), cend(),
                           bind(&Expr_place::is_token, _1));
    }

    Expr& Expr::flatten()
    {
        if (_is_flatten) return *this;
        _is_flatten = true;
        Places places;
        places.reserve(size()*2);
        for (auto& e : _places) {
            if (e->is_token()) {
                places.emplace_back(move(e));
                continue;
            }
            auto& subexpr = ptr_to_expr(e).flatten();
            move(subexpr.begin(), subexpr.end(), std::back_inserter(places));
        }
        _places = move(places);
        return *this;
    }
}
