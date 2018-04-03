#ifndef ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
#define ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430

#include "sos.hpp"

using namespace std::placeholders;

namespace SOS {
    class Expr_place {
    public:
        using Token = string;
        template <typename T>
        using Expr_ptr_t = unique_ptr<T>;
        using Expr_place_ptr = Expr_ptr_t<Expr_place>;

        virtual ~Expr_place() = default;
        virtual Expr_place_ptr clone() const = 0;

        virtual bool is_token() const noexcept = 0;
        virtual explicit operator string () const noexcept = 0;

        friend string to_string(const Expr_place& rhs)
            { return move((string)rhs); }
        friend ostream& operator <<(ostream& os, const Expr_place& rhs)
            { return (os << to_string(rhs)); }
        friend bool operator ==(const Expr_place& lhs, const Expr_place& rhs)
            { return (string)lhs == (string)rhs; }
        friend bool operator !=(const Expr_place& lhs, const Expr_place& rhs)
            { return !(lhs == rhs); }
    protected:
        template <typename T>
        static Expr_ptr_t<T> new_place(T&& place_)
            { return make_unique<T>(forward<T>(place_)); }
    };

    class Expr_token : public Expr_place {
    public:
        virtual ~Expr_token() = default;
        virtual Expr_place_ptr clone() const override final
            { return new_place(Expr_token(*this)); }
        Expr_token(const string& input) : _token(input) { }

        const Token& token() const { return _token; }
        template <typename Arg>
        bool get_value_check(Arg& arg) const
            { istringstream iss(_token); return (bool)(iss >> arg); }
        template <typename Arg>
        Arg get_value() const
            { Arg arg; get_value_check(arg); return arg; }
        template <typename Arg>
        bool is_value() const
            { Arg v; return get_value_check(v); }

        virtual bool is_token() const noexcept override final
            { return true; }
        virtual explicit operator string () const noexcept override final
            { return move(token()); }
    private:
        Token _token;
    };

    class Expr : public Expr_place {
    public:
        template <typename Arg>
        class Eval;
        template <typename Arg>
        using Elems = vector<Arg>;

        Expr() = default;
        virtual ~Expr() = default;
        virtual Expr_place_ptr clone() const override
            { return new_place(Expr(*this)); }
        Expr(const Expr& rhs);
        Expr& operator =(const Expr& rhs);
        Expr(Expr&& rhs) = default;
        Expr& operator =(Expr&& rhs) = default;
        Expr(const string& input) : Expr(istringstream(input)) { }
        Expr(initializer_list<Expr_place_ptr> list);
        void swap(Expr& rhs) { std::swap(_places, rhs._places); }

        virtual bool is_token() const noexcept override
            { return false; }
        virtual explicit operator string () const noexcept override;

        size_t size() const noexcept { return _places.size(); }
        bool empty() const noexcept { return size() == 0; }
        const Expr_place_ptr& operator [](int idx) const
            { return _places[idx]; }
        Expr_place_ptr& operator [](int idx)
            { return _places[idx]; }
        const Expr_place_ptr& cfront() const { return _places.front(); }
        const Expr_place_ptr& cback() const { return _places.back(); }
        Expr_place_ptr& front() { return _places.front(); }
        Expr_place_ptr& back() { return _places.back(); }
        const auto cbegin() const { return std::cbegin(_places); }
        const auto cend() const { return std::cend(_places); }
        const auto begin() const { return std::begin(_places); }
        const auto end() const { return std::end(_places); }
        auto begin() { return std::begin(_places); }
        auto end() { return std::end(_places); }
        const Expr_token& cto_token(int idx) const
            { return cptr_to_token((*this)[idx]); }
        const Expr& cto_expr(int idx) const
            { return cptr_to_expr((*this)[idx]); }

        Expr& simplify() noexcept;
        Expr& to_binary(const Token& neutral = "0");
        bool is_flat() const
            { return std::all_of(cbegin(), cend(),
                                 bind(&Expr_place::is_token, _1)); }
        template <typename Arg>
        bool has_values() const;
        Expr& flatten();
        template <typename Arg>
        Elems<Arg> flat_transform() const;

        template <typename Arg>
        Eval<Arg> get_eval(typename Eval<Arg>::Param_keys param_keys_ = {})
            { return {to_binary(), move(param_keys_)}; }
        template <typename Arg>
        Eval<Arg> cget_eval(typename Eval<Arg>::Param_keys param_keys_ = {}) const
            { return {*this, move(param_keys_)}; }
        template <typename Arg>
        Arg eval(initializer_list<Arg> list,
            typename Eval<Arg>::Param_keys param_keys_ = {})
            { return get_eval<Arg>(move(param_keys_))(move(list)); }
        template <typename Arg>
        Arg eval(typename Eval<Arg>::Param_values param_values_,
            typename Eval<Arg>::Param_keys param_keys_ = {})
            { return get_eval<Arg>(move(param_keys_))(move(param_values_)); }
        template <typename Arg>
        Arg ceval(initializer_list<Arg> list,
            typename Eval<Arg>::Param_keys param_keys_ = {}) const
            { return cget_eval<Arg>(move(param_keys_))(move(list)); }
        template <typename Arg>
        Arg ceval(typename Eval<Arg>::Param_values param_values_,
            typename Eval<Arg>::Param_keys param_keys_ = {}) const
            { return cget_eval<Arg>(move(param_keys_))(move(param_values_)); }
    protected:
        using Places = Elems<Expr_place_ptr>;

        Expr(istringstream& iss, unsigned depth = 0);
        Expr(istringstream&& iss) : Expr(iss) { }

        template <typename T>
        void add_place_ptr(T&& place_ptr_)
            { _places.emplace_back(forward<T>(place_ptr_)); }
        template <typename T>
        void add_new_place(T&& place_)
            { add_place_ptr(new_place(forward<T>(place_))); }
        static const Expr_token& cptr_to_token(const Expr_place_ptr& place_ptr)
            { return static_cast<Expr_token&>(*place_ptr); }
        static const Expr& cptr_to_expr(const Expr_place_ptr& place_ptr)
            { return static_cast<Expr&>(*place_ptr); }
        static Expr_token& ptr_to_token(Expr_place_ptr& place_ptr)
            { return static_cast<Expr_token&>(*place_ptr); }
        static Expr& ptr_to_expr(Expr_place_ptr& place_ptr)
            { return static_cast<Expr&>(*place_ptr); }
        Expr_token& to_token(int idx)
            { return ptr_to_token((*this)[idx]); }
        Expr& to_expr(int idx)
            { return ptr_to_expr((*this)[idx]); }
    private:
        Expr& simplify_top() noexcept;
        Expr& simplify_rec() noexcept;

        Places _places;
        bool _is_simplified{false};
        bool _is_binary{false};
        bool _is_flatten{false};
    };
}

#include "expr.tpp"

#endif // ___SOS_EXPR_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
