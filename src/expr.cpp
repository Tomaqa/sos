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

    Expr::Expr(istringstream& iss, int depth)
        : Expr()
    {
        char c;
        string str;
        ostringstream oss;
        bool closed = false;
        iss >> std::noskipws;
        while (iss >> c) {
            if (!isprint(c)) {
                if (!c) break;
                throw Error("Unexpected non-printable character ("s + to_string((int)c) + ")");
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
                throw Error("Unexpected closing brace in top level expression.");
            }
            oss << c;
            char c2 = iss.peek();
            if (isspace(c2) || c2 == '(') {
                add_new_place(Expr_token(oss.str()));
                oss.str("");
            }
        }

        if (!closed && depth > 0) {
            throw Error("Closing brace at level " + to_string(depth) + " not found.");
        }

        if (!oss.str().empty()) {
            add_new_place(Expr_token(oss.str()));
        }

        simplify();
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
        if (empty()) return *this;
        for (auto& e : *this) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Expr&>(*e);
            if (e_cast.simplify().size() == 1) {
                e = move(e_cast.first());
            }
        }
        if (size() == 1 && !cfirst()->is_token()) {
            _places = move(static_cast<Expr&>(*first())._places);
        }
        return *this;
    }

    Expr& Expr::to_binary(const Token& neutral)
    {
        if (_is_binary) return *this;
        if (size() <= 1) {
            throw Error("Expression has not at least 2 arguments.");
        }
        if (!cfirst()->is_token()) {
            throw Error("First argument of each expression should be single token.");
        }
        if (size() == 2) {
            add_new_place(Expr_token(neutral));
            std::swap(_places[1], _places[2]);
        }
        else if (size() > 3) {
            Expr subexpr{cfirst()->clone()};
            for (auto&& it = begin()+2, eit = end(); it != eit; ++it) {
                subexpr.add_place_ptr(move(*it));
            }
            _places.erase(begin()+3, end());
            _places[2] = new_place(move(subexpr.to_binary()));
        }
        for (auto& e : *this) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Expr&>(*e);
            e_cast.to_binary();
        }
        _is_binary = true;
        return *this;
    }
}
