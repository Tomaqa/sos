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
        template <typename T>
        using Expr_ptr_t = unique_ptr<T>;
        using Expr_ptr = Expr_ptr_t<Expr>;

        virtual ~Expr() = default;
        virtual Expr_ptr clone() const = 0;

        virtual bool is_token() const noexcept = 0;
        virtual explicit operator string () const noexcept = 0;

        friend ostream& operator <<(ostream& os, const Expr& rhs)
            { return (os << (string)rhs); }
    protected:
        template <typename T>
        static Expr_ptr_t<T> new_expr(T&& expr)
            { return make_unique<T>(std::forward<T>(expr)); }
    };

    class Parser::Token : public Parser::Expr {
    public:
        virtual ~Token() = default;
        virtual Expr_ptr clone() const override final
            { return new_expr(Token(*this)); }
        Token(const string& input) : _token(input) { }

        virtual bool is_token() const noexcept override final
            { return true; }
        virtual explicit operator string () const noexcept override final
            { return _token; }
    private:
        Token_t _token;
    };

    class Parser::Exprs : public Parser::Expr {
    public:
        Exprs() = default;
        virtual ~Exprs() = default;
        virtual Expr_ptr clone() const override
            { return new_expr(Exprs(*this)); }
        Exprs(const Exprs& rhs);
        Exprs& operator =(const Exprs& rhs);
        Exprs(Exprs&& rhs) = default;
        Exprs& operator =(Exprs&& rhs) = default;
        Exprs(const string& input) : Exprs(istringstream(input)) { }
        Exprs(initializer_list<Expr_ptr> list);

        virtual bool is_token() const noexcept override
            { return false; }
        virtual explicit operator string () const noexcept override;

        size_t size() const noexcept { return _exprs.size(); }
        bool empty() const noexcept { return size() == 0; }
        const Expr_ptr& first() const { return _exprs[0]; }

        Exprs& simplify() noexcept;
        Exprs& to_binary(const Token_t& neutral = "0");
    protected:
        using Exprs_t = vector<Expr_ptr>;

        Exprs(istringstream& iss, int depth = 0);
        Exprs(istringstream&& iss) : Exprs(iss) { }

        template <typename T>
        void add_expr_ptr(T&& expr_ptr)
            { _exprs.emplace_back(std::forward<T>(expr_ptr)); }
        template <typename T>
        void add_new_expr(T&& expr)
            { add_expr_ptr(new_expr(std::forward<T>(expr))); }
        Expr_ptr& first() { return _exprs[0]; }
    private:
        Exprs_t _exprs;
    };
}

#endif // ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
