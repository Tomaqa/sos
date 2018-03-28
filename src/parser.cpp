#include "parser.h"

namespace SOS {
    istringstream Parser::flat_extract_braces(istringstream& iss)
    {
        string str;
        iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
        getline(iss, str, ')');
        return istringstream(str);
    }

    Parser::Exprs::Exprs(istringstream& iss, int depth)
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

    Parser::Exprs::Exprs(const Parser::Exprs& rhs)
    {
        _exprs.reserve(rhs.size());
        for (auto& e : rhs._exprs) {
            add_expr_ptr(e->clone());
        }
    }

    Parser::Exprs& Parser::Exprs::operator =(const Parser::Exprs& rhs)
    {
        Exprs tmp(rhs);
        swap(_exprs, tmp._exprs);
        return *this;
    }

    Parser::Exprs::operator string () const noexcept
    {
        string str("( ");
        for (auto& e : _exprs) {
            str += (string)*e + " ";
        }
        return (str += ")");
    }

    void Parser::Exprs::simplify() noexcept
    {
        if (empty()) return;
        for (auto& e : _exprs) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Exprs&>(*e);
            e_cast.simplify();
            if (e_cast.size() == 1) {
                e = move(e_cast.first());
            }
        }
        if (size() == 1 && !first()->is_token()) {
            _exprs = move(static_cast<Exprs&>(*first())._exprs);
        }
    }

    void Parser::Exprs::to_binary(const Token_t& neutral)
    {
        if (size() <= 1) {
            throw Error("Expression has not at least 2 arguments.");
        }
        if (!first()->is_token()) {
            throw Error("First argument of each expression should be single token.");
        }
        for (auto& e : _exprs) {
            if (e->is_token()) continue;
            auto& e_cast = static_cast<Exprs&>(*e);
            e_cast.to_binary();
        }
        if (size() == 2){
            add_new_expr(Token(neutral));
            return;
        }
        if (size() == 3) return;
        // auto&& b_it = begin(_exprs)+2;
        // Exprs_t exprs{move(new_expr(*move(begin(_exprs)))), move(new_expr(move(*begin(_exprs)+1)))};
        // Exprs_t exprs{move(new_expr(Token(""))), move(new_expr(Token("")))};
        // Exprs_t exprs{new_expr(Token("")), new_expr(Token(""))};
        // exprs.emplace_back(new_expr(move(_exprs[0])));
        // const auto& oper = static_cast<Token&>(*first());
        // const auto& oper = static_cast<const Token&>(*first());
        // auto&& oper = static_cast<Token&&>(*first());
        // Exprs_t exprs;
        // exprs.emplace_back(new_expr(move(oper)));
        for (auto&& it = begin(_exprs)+2, eit = end(_exprs); it != eit; ++it) {

        }
    }
}
