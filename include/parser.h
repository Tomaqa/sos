#ifndef ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
#define ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430

#include "sos.h"

#include <regex>

using std::regex;
using std::regex_match;

namespace SOS {
    class Parser {
    public:
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
    };

    class Parser::Expr {
    public:
        virtual ~Expr() = default;

        virtual bool is_token() const noexcept = 0;
        virtual void simplify() noexcept = 0;
        virtual explicit operator string () const noexcept = 0;

        friend ostream& operator <<(ostream& os, const Expr& rhs)
            { return (os << (string)rhs); }
    };

    class Parser::Token : public Parser::Expr {
    public:
        Token(const string& input) : _token(input) { }
        virtual ~Token() = default;

        virtual bool is_token() const noexcept override final
            { return true; }
        virtual void simplify() noexcept override final { }
        virtual explicit operator string () const noexcept override final
            { return _token; }
    private:
        Token_t _token;
    };


    class Parser::Exprs : public Parser::Expr {
    public:
        template <typename T>
        using Expr_ptr = unique_ptr<T>;
        using Expr_t = Expr_ptr<Expr>;

        Exprs(const string& input) : Exprs(istringstream(input)) { }
        virtual ~Exprs() = default;
        Exprs(const Exprs& rhs) = delete;
        Exprs& operator =(const Exprs& rhs) = delete;
        Exprs(Exprs&& rhs) = default;
        Exprs& operator =(Exprs&& rhs) = default;

        virtual bool is_token() const noexcept override
            { return false; }
        virtual void simplify() noexcept override;
        virtual explicit operator string () const noexcept override;

        size_t size() const noexcept { return _contents.size(); }
        bool empty() const noexcept { return size() == 0; }
        // const Expr& first() const { return *_contents[0]; }
        // const Expr* first() const { return _contents[0]; }
        const Expr_t& first() const { return _contents[0]; }
    protected:
        using Exprs_t = vector<Expr_t>;

        Exprs(istringstream& iss, int depth = 0);
        Exprs(istringstream&& iss) : Exprs(iss) { }

        template <typename T>
        void add_expr(T&& expr)
            { _contents.emplace_back(make_unique<T>(move(expr))); }
        // Expr& first() { return *_contents[0]; }
        // Expr* first() { return _contents[0]; }
        Expr_t& first() { return _contents[0]; }
    private:
        Exprs_t _contents;
    };
}

#endif // ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
