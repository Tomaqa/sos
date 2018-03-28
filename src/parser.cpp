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
                add_expr(Exprs(iss, depth+1));
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
                add_expr(Token(oss.str()));
                oss.str("");
            }
        }

        if (!closed && depth > 0) {
            throw Error("Closing brace at level " + to_string(depth) + " not found.");
        }

        if (!oss.str().empty()) {
            add_expr(Token(oss.str()));
        }

        simplify();
    }

    void Parser::Exprs::simplify() noexcept
    {
        if (empty()) return;
        // for (auto& e : _contents) {
            // e.simplify();
        // for (auto e : _contents) {
            // e->simplify();
            // auto ptr = dynamic_cast<Parser::Expr*>(&e);
            // if (ptr) ptr->simplify();
        // }
        // if (is_token() && !first().empty()) {
        //     _contents = move(first()._contents);
        // }
        // if (size() > 1) return;
        // ! potrebuju byt o uroven vys, jinak bych prirazoval sam sobe ..
        // if (first().empty()) {
            // _contents = move(first()._contents);
        // }
        // if (size() > 1) return;
        for (auto& e : _contents) {
            e->simplify();
            if (!e->is_token()) {
                // auto& e_cast = static_cast<Expr_ptr<Exprs>>(e);
                // auto& e_cast = dynamic_cast<Expr_ptr<Exprs>>(e);
                // if (e_cast->size() == 1) {
                    // e_cast = move(e_cast->first());
                // }
                // auto& e_cast = static_cast<const Exprs&>(*e);

                // const auto& e_cast = static_cast<const Expr_ptr<Exprs>&>(e);
                auto& e_cast = static_cast<Exprs&>(*e);
                if (e_cast.size() == 1) {
                    cout << "?" << (string)*e << endl;
                    // e = move(e_cast.first());
                    // *e = move(e_cast.first());
                    // *e = e_cast.first();
                    // e = make_unique(e_cast.first());
                    // e = e_cast.first();
                    e = move(e_cast.first());
                    cout << "!" << (string)*e << endl;
                }
            }
        }
    }

    Parser::Exprs::operator string () const noexcept
    {
        string str("( ");
        for (auto& e : _contents) {
            str += (string)*e + " ";
        }
        return (str += ")");
    }
}
