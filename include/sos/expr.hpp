#pragma once

#include "sos.hpp"
#include "util.hpp"

#include <memory>

namespace SOS {
    using namespace Util;

    using std::unique_ptr;
    using std::shared_ptr;
    using std::make_unique;
    using std::make_shared;

    class Expr_place {
    public:
        using Token = string;
        template <typename T> using Expr_ptr_t = unique_ptr<T>;
        using Expr_place_ptr = Expr_ptr_t<Expr_place>;

        virtual ~Expr_place()                                       = default;
        virtual Expr_place_ptr clone() const                              = 0;

        // virtual bool is_token() const noexcept                            = 0;
        virtual bool is_etoken() const noexcept                           = 0;
        virtual explicit operator string () const noexcept                = 0;
        friend string to_string(const Expr_place& rhs);
        friend ostream& operator <<(ostream& os, const Expr_place& rhs);

        friend bool operator ==(const Expr_place& lhs, const Expr_place& rhs);
        friend bool operator !=(const Expr_place& lhs, const Expr_place& rhs);
    protected:
        template <typename T> static Expr_ptr_t<T> new_place(T&& place_);
    };

    class Expr_token : public Expr_place {
    public:
        Expr_token()                                                 = delete;
        virtual ~Expr_token()                                       = default;
        virtual Expr_place_ptr clone() const override final;
        Expr_token(const Token& token);

        const Token& ctoken() const                         { return _token; }
        Token& token()                                      { return _token; }
        static const Token& check_token(const Token& token);
        static bool valid_token(const Token& token);

        template <typename Arg> bool get_value_check(Arg& arg) const;
        template <typename Arg> Arg get_value() const;
        template <typename Arg> bool is_value() const;

        // virtual bool is_token() const noexcept override final { return true; }
        virtual bool is_etoken() const noexcept override final
                                                              { return true; }
        virtual explicit operator string () const noexcept override final
                                                    { return move(ctoken()); }
    private:
        Token _token;
    };

    class Expr : public Expr_place {
    public:
        template <typename Arg> class Eval;
        template <typename Arg> using Elems = vector<Arg>;
        using Tokens = Elems<Token>;
        using Exprs = Elems<Expr>;
        using Places = Elems<Expr_place_ptr>;

        Expr()                                                      = default;
        virtual ~Expr()                                             = default;
        virtual Expr_place_ptr clone() const override;
        Expr(const Expr& rhs);
        Expr& operator =(const Expr& rhs);
        Expr(Expr&& rhs)                                            = default;
        Expr& operator =(Expr&& rhs)                                = default;
        Expr(const string& input);
        Expr(initializer_list<Expr_place_ptr> list);

        // virtual bool is_token() const noexcept override      { return false; }
        virtual bool is_etoken() const noexcept override     { return false; }
        virtual explicit operator string () const noexcept override;

        const Places& cplaces() const                      { return _places; }
        // !
        Places& places()                                   { return _places; }
        size_t size() const noexcept              { return cplaces().size(); }
        bool empty() const noexcept                    { return size() == 0; }

        const Expr_place_ptr& operator [](int idx) const;
        Expr_place_ptr& operator [](int idx);
        const Expr_place_ptr& cfront() const;
        const Expr_place_ptr& cback() const;
        Expr_place_ptr& front();
        Expr_place_ptr& back();
        // static const Expr_token&
        //     cptr_to_token(const Expr_place_ptr& place_ptr);
        static const Expr_token&
            cptr_to_etoken(const Expr_place_ptr& place_ptr);
        static const Expr&
            cptr_to_expr(const Expr_place_ptr& place_ptr);
        // static Expr_token& ptr_to_token(Expr_place_ptr& place_ptr);
        static Expr_token& ptr_to_etoken(Expr_place_ptr& place_ptr);
        static Expr& ptr_to_expr(Expr_place_ptr& place_ptr);
        // const Expr_token& cto_token(int idx) const;
        const Expr_token& cto_etoken(int idx) const;
        const Expr& cto_expr(int idx) const;
        // Expr_token& to_token(int idx);
        Expr_token& to_etoken(int idx);
        Expr& to_expr(int idx);
        const auto cbegin() const           { return std::cbegin(cplaces()); }
        const auto cend() const               { return std::cend(cplaces()); }
        const auto begin() const             { return std::begin(cplaces()); }
        const auto end() const                 { return std::end(cplaces()); }
        auto begin()                          { return std::begin(places()); }
        auto end()                              { return std::end(places()); }

        template <typename T> void add_new_place(T&& place_);

        Expr& simplify() noexcept;
        Expr& to_binary(const Token& neutral = "0");
        bool is_flat() const;
        bool is_deep() const;
        template <typename Arg> bool has_values() const;
        Expr& flatten();
        Tokens transform_to_tokens() const;
        Exprs transform_to_exprs() const;
        template <typename Arg> Elems<Arg> transform_to_args() const;

        template <typename Arg> Eval<Arg>
            get_eval(typename Eval<Arg>::Param_keys param_keys_ = {});
        template <typename Arg> Eval<Arg>
            get_eval(typename Eval<Arg>::Param_keys_ptr param_keys_ptr_);
        template <typename Arg> Eval<Arg>
            get_eval(typename Eval<Arg>::Param_keys_ptr param_keys_ptr_,
                     typename Eval<Arg>::Param_values_ptr param_values_ptr_);
    protected:
        Expr(istringstream& iss, unsigned depth = 0);
        Expr(istringstream&& iss)                              : Expr(iss) { }

        template <typename T> void add_place_ptr(T&& place_ptr_);
    private:
        Expr& simplify_top() noexcept;
        Expr& simplify_rec() noexcept;

        Places _places;
        // ? reimplement to 'Flag's ?
        bool _is_simplified{false};
        bool _is_binary{false};
        bool _is_flatten{false};
    };
}

#include "expr.tpp"
