#ifndef ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
#define ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430

#include "sos.h"

#include <regex>

using std::regex;
using std::regex_match;

namespace SOS {
    class Parser {
    public:
        // using Token = string;
        // using Tokens = vector<Token>;
        // using Expr = vector<Tokens>;
        // using TokenType = string;
        // template <typename T>
        // using ExprContainer = vector<T>;

        class Expr;
        class Token;
        class Exprs;

        static constexpr const char* re_float = "[+-]?\\d*\\.?\\d+";
        template <typename Arg, typename F>
        static const map<const char, F> oper = {
            {'+', [](Arg a, Arg b){ return a + b; }},
            {'-', [](Arg a, Arg b){ return a - b; }},
            {'*', [](Arg a, Arg b){ return a * b; }},
            {'/', [](Arg a, Arg b){ return a / b; }},
        };
        // std::function

        static istringstream flat_extract_braces(istringstream& iss);
        static istringstream flat_extract_braces(istringstream&& iss)
            { return move(flat_extract_braces(iss)); }
    protected:
        using Token_t = string;
        // template <typename T>
        // using ExprContainer = vector<T>;
        // using Exprs_t = vector<unique_ptr<Expr>>;
    };

    // class Parser::Token {
    // public:
    //     Token(const string& input) : _token(input) { }

    //     friend ostream& operator <<(ostream& os, const Parser::Token& rhs)
    //         { return (os << rhs._token); }
    // protected:
    //     Token_t _token;
    // };


    // // class Parser::Expr {
    // class Parser::Expr : public Parser::Token {
    // public:
    //     Expr(const string& input) : Expr(istringstream(input)) { }

    //     size_t size() const { return _contents.size(); }
    //     bool empty() const { return size() == 0; }
    //     bool is_token() const { return size() == 1; }
    //     // const Expr& first() const { return _contents[0]; }
    //     const Token& first() const { return _contents[0]; }

    //     friend ostream& operator <<(ostream& os, const Parser::Expr& rhs);
    // protected:
    //     Expr(istringstream& iss, int depth = 0);
    //     Expr(istringstream&& iss) : Expr(iss) { }

    //     void add_token (const string& token)
    //         { _contents.emplace_back(Token(token)); }
    //     // Expr& first() { return _contents[0]; }
    //     Token& first() { return _contents[0]; }
    //     void simplify();
    // private:
    //     // ExprContainer<Expr> _contents;
    //     ExprContainer<Token> _contents;
    // };

    class Parser::Expr {
    public:
        virtual bool is_token() const noexcept = 0;
        virtual void simplify() noexcept = 0;
        virtual void print(ostream& os) const = 0;

        friend ostream& operator <<(ostream& os, const Expr& rhs)
            { rhs.print(os); return os; }
    };

    class Parser::Token : public Parser::Expr {
    public:
        Token(const string& input) : _token(input) { }

        virtual bool is_token() const noexcept override final
            { return true; }
        virtual void simplify() noexcept override final { }
        virtual void print(ostream& os) const override final
            { os << _token; }
    private:
        Token_t _token;
    };


    class Parser::Exprs : public Parser::Expr {
    public:
        Exprs(const string& input) : Exprs(istringstream(input)) { }

        virtual bool is_token() const noexcept override
            { return false; }
        virtual void simplify() noexcept override;
        virtual void print(ostream& os) const override;

        size_t size() const noexcept { return _contents.size(); }
        bool empty() const noexcept { return size() == 0; }
        // const Expr& first() const noexcept { return _contents[0]; }
        const Expr& first() const { return *_contents[0]; }
    protected:
        Exprs(istringstream& iss, int depth = 0);
        Exprs(istringstream&& iss) : Exprs(iss) { }

        template <typename T>
        void add_expr(T&& expr)
            { _contents.emplace_back(make_unique<T>(move(expr))); }
        // Expr& first() noexcept { return _contents[0]; }
        Expr& first() { return *_contents[0]; }
    private:
        // ExprContainer<Expr*> _contents;
        vector<unique_ptr<Expr>> _contents;
    };
}

#endif // ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
