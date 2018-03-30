#ifndef ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
#define ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430

#include "sos.hpp"

#include <regex>
#include <functional>

using std::regex;
using std::regex_match;

using std::function;
using std::bind;

using namespace std::placeholders;

namespace SOS {
    class Expr {
    public:
        using Token_t = string;
        template <typename T>
        using Expr_ptr_t = unique_ptr<T>;
        using Expr_ptr = Expr_ptr_t<Expr>;

        static constexpr const char* re_float = "[+-]?\\d*\\.?\\d+";

        template <typename Arg>
        class Eval;
        template <typename Arg>
        class Oper;

        virtual ~Expr() = default;
        virtual Expr_ptr clone() const = 0;

        virtual bool is_token() const noexcept = 0;
        virtual explicit operator string () const noexcept = 0;

        friend ostream& operator <<(ostream& os, const Expr& rhs)
            { return (os << (string)rhs); }

        static istringstream flat_extract_braces(istringstream& iss);
        static istringstream flat_extract_braces(istringstream&& iss)
            { return move(flat_extract_braces(iss)); }
    protected:
        template <typename T>
        static Expr_ptr_t<T> new_expr(T&& expr)
            { return make_unique<T>(std::forward<T>(expr)); }
    };

    class Token : public Expr {
    public:
        virtual ~Token() = default;
        virtual Expr_ptr clone() const override final
            { return new_expr(Token(*this)); }
        Token(const string& input) : _token(input) { }

        Token_t token() const { return _token; }
        template <typename T>
        bool value(T& var) const
            { istringstream iss(_token); return (bool)(iss >> var); }
        template <typename T>
        bool is_value() const
            { T v; return value(v); }

        virtual bool is_token() const noexcept override final
            { return true; }
        virtual explicit operator string () const noexcept override final
            { return move(token()); }
    private:
        Token_t _token;
    };

    class Exprs : public Expr {
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
        void swap(Exprs& rhs) { std::swap(_exprs, rhs._exprs); }

        virtual bool is_token() const noexcept override
            { return false; }
        virtual explicit operator string () const noexcept override;

        size_t size() const noexcept { return _exprs.size(); }
        bool empty() const noexcept { return size() == 0; }
        const Expr_ptr& operator [] (size_t idx) const
            { return _exprs[idx]; }
        const Expr_ptr& first() const { return (*this)[0]; }
        auto begin() { return _exprs.begin(); }
        const auto begin() const { return _exprs.begin(); }
        auto end() { return _exprs.end(); }
        const auto end() const { return _exprs.end(); }

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
        Expr_ptr& operator [] (size_t idx)
            { return _exprs[idx]; }
        Expr_ptr& first() { return (*this)[0]; }
    private:
        Exprs_t _exprs;
    };
}

#endif // ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
