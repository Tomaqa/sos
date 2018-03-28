#include "parser.h"

namespace SOS {
    istringstream Parser::flat_extract_braces(istringstream& iss)
    {
        string str;
        iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
        getline(iss, str, ')');
        return istringstream(str);
    }

    // Parser::Expr::Expr(istringstream& iss, int depth)
        // : Token("")
    Parser::Exprs::Exprs(istringstream& iss, int depth)
    {
        cout << "I:>" << iss.str() << "<" << endl;
        iss >> std::noskipws;
        // ostringstream oss;
        char c;
        string str;
        bool closed = false;
        // while (iss >> c) {
        // while (iss.get(c).good()) {
        // while (!iss.get(c).eof()) {
        int k = 0;
        while (iss.good() && !iss.eof()) {
            cout << ++k << endl;
            iss >> c;
            cout << "<" << iss.rdstate() << ">" << endl;
            cout << "[" << c << "]" << "(" << (int)c << ")" << endl;
            if (!iss.good() || iss.eof()) break;
            if (!isprint(c)) {
                if (!c) break;
                throw Error("Unexpected non-printable character ("s + to_string((int)c) + ")");
            }
            if (isspace(c)) {
                // if (!oss.str().empty()) {
                //     _contents.emplace_back(oss.str());
                //     oss.str("");
                // }
                continue;
            }
            if (c == '(') {
                // _contents.emplace_back(Expr(iss, depth+1));
                continue;
            }
            if (c == ')') {
                if (depth > 0) {
                    closed = true;
                    break;
                }
                throw Error("Unexpected closing brace in top level expression.");
            }
            // oss << c;
            // cout << "O:>" << oss.str() << "<" << endl;
            iss.unget() >> str;
            // add_token(str);
            // add_expr(Token(str));
            // _contents.emplace_back(Token(str));
            // _contents.emplace_back(make_unique<Token>(Token(str)));
            add_expr(Token(str));
        }

        if (!closed && depth > 0) {
            throw Error("Closing brace at level " + to_string(depth) + " not found.");
        }

        // if (!oss.str().empty()) {
        //     _contents.emplace_back(oss.str());
        // }

        cout << "{" << size() << "}" << endl;

        // simplify();
    }

    // void Parser::Expr::simplify()
    void Parser::Exprs::simplify() noexcept
    {
        if (empty()) return;
        for (auto& e : _contents) {
            // e.simplify();
        // for (auto e : _contents) {
            e->simplify();
            // auto ptr = dynamic_cast<Parser::Expr*>(&e);
            // if (ptr) ptr->simplify();
        }
        // if (is_token() && !first().empty()) {
        //     _contents = move(first()._contents);
        // }
        if (size() > 1) return;
        // ! potrebuju byt o uroven vys, jinak bych prirazoval sam sobe ..
        // if (first().empty()) {
            // _contents = move(first()._contents);
        // }
    }

    // ostream& operator <<(ostream& os, const Parser::Expr& rhs)
    // Parser::Exprs::print(ostream& os) const
    // {
    //     if (rhs.is_token()) {
    //         os << rhs.first();
    //     }
    //     else {
    //         os << "( ";
    //         for (auto& e : rhs._contents) {
    //             os << e << " ";
    //         }
    //         os << ")";
    //     }
    //     return os;
    // }
    void Parser::Exprs::print(ostream& os) const
    {
        os << "( ";
        for (auto& e : _contents) {
            // os << e << " ";
        // for (auto e : _contents) {
            os << *e << " ";
        }
        os << ")";
    }
}
