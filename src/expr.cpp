#include "expr.hpp"

namespace SOS {
    istringstream Expr::flat_extract_braces(istringstream& iss)
    {
        string str;
        iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
        getline(iss, str, ')');
        return istringstream(str);
    }

    Exprs::Exprs(const Exprs& rhs)
    {
        _exprs.reserve(rhs.size());
        for (const auto& e : rhs) {
            add_expr_ptr(e->clone());
        }
    }

    Exprs& Exprs::operator =(const Exprs& rhs)
    {
        Exprs tmp(rhs);
        swap(tmp);
        return *this;
    }

    Exprs::Exprs(istringstream& iss, int depth)
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
                add_new_expr(Exprs(iss, depth+1));
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
                add_new_expr(Token(oss.str()));
                oss.str("");
            }
        }

        if (!closed && depth > 0) {
            throw Error("Closing brace at level " + to_string(depth) + " not found.");
        }

        if (!oss.str().empty()) {
            add_new_expr(Token(oss.str()));
        }

        simplify();
    }

    Exprs::Exprs(initializer_list<Expr_ptr> list)
    {
        for (const auto& e : list) {
            add_expr_ptr(e->clone());
        }
    }

    Exprs::operator string () const noexcept
    {
        string str("( ");
        for (const auto& e : *this) {
            str += (string)*e + " ";
        }
        return (str += ")");
    }

    Exprs& Exprs::simplify() noexcept
    {
        if (empty()) return *this;
        for (auto& e : *this) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Exprs&>(*e);
            if (e_cast.simplify().size() == 1) {
                e = move(e_cast.first());
            }
        }
        if (size() == 1 && !first()->is_token()) {
            _exprs = move(static_cast<Exprs&>(*first())._exprs);
        }
        return *this;
    }

    Exprs& Exprs::to_binary(const Token_t& neutral)
    {
        if (size() <= 1) {
            throw Error("Expression has not at least 2 arguments.");
        }
        if (!first()->is_token()) {
            throw Error("First argument of each expression should be single token.");
        }
        if (size() == 2) {
            add_new_expr(Token(neutral));
            std::swap(_exprs[1], _exprs[2]);
        }
        else if (size() > 3) {
            Exprs subexprs{first()->clone()};
            for (auto&& it = begin()+2, eit = end(); it != eit; ++it) {
                subexprs.add_expr_ptr(move(*it));
            }
            _exprs.erase(begin()+3, end());
            _exprs[2] = new_expr(move(subexprs.to_binary()));
        }
        for (auto& e : *this) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Exprs&>(*e);
            e_cast.to_binary();
        }
        return *this;
    }
}
