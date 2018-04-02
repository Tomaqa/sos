#include "expr.hpp"

namespace SOS {
    Expr::Expr(const Expr& rhs)
        : _is_binary(rhs._is_binary)
    {
        _places.reserve(rhs.size());
        for (const auto& e : rhs) {
            add_place_ptr(e->clone());
        }
    }

    Expr& Expr::operator =(const Expr& rhs)
    {
        Expr tmp(rhs);
        swap(tmp);
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
                expect(c == 0, "Unexpected non-printable character ("s + to_string((int)c) + ")");
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
                expect(depth > 0, "Unexpected closing brace in top level expression.");
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
            str += (string)*e + " ";
        }
        return (str += ")");
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
