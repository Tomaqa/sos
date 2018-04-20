#pragma once

#include "sos.hpp"
#include "util.hpp"

#include <memory>
#include <list>

namespace SOS {
    using namespace Util;

    using std::unique_ptr;
    using std::shared_ptr;
    using std::make_unique;
    using std::make_shared;

    using std::list;

    class Expr_place {
    public:
        using Token = string;
        template <typename T> using Expr_ptr_t = unique_ptr<T>;
        using Expr_place_ptr = Expr_ptr_t<Expr_place>;

        virtual ~Expr_place()                                       = default;
        virtual Expr_place_ptr clone() const                              = 0;

        virtual bool is_etoken() const noexcept                           = 0;
        virtual explicit operator string () const noexcept                = 0;
        friend string to_string(const Expr_place& rhs);
        friend ostream& operator <<(ostream& os, const Expr_place& rhs);

        friend bool operator ==(const Expr_place& lhs, const Expr_place& rhs);
        friend bool operator !=(const Expr_place& lhs, const Expr_place& rhs);
    protected:
        template <typename T> static Expr_ptr_t<T> new_place(T&& place);
    };

    class Expr_token : public Expr_place {
    public:
        Expr_token()                                                 = delete;
        virtual ~Expr_token()                                       = default;
        virtual Expr_place_ptr clone() const override final;
        Expr_token(Token token);

        template <typename... Args>
            static Expr_ptr_t<Expr_token> new_etoken(Args&&... args);

        const Token& ctoken() const                         { return _token; }
        Token& token()                                      { return _token; }
        static const Token& check_token(const Token& token);
        static bool valid_token(const Token& token);

        template <typename Arg> bool get_value_valid(Arg& arg) const;
        template <typename Arg> Arg get_value() const;
        template <typename Arg> Arg get_value_check() const;
        template <typename Arg> bool is_valid_value() const;

        virtual bool is_etoken() const noexcept override final
                                                              { return true; }
        virtual explicit operator string () const noexcept override final
                                                          { return ctoken(); }
    private:
        Token _token;
    };

    class Expr : public Expr_place {
    public:
        template <typename Arg> class Eval;
        template <typename Arg> using Elems = vector<Arg>;
        using Tokens = Elems<Token>;
        using Exprs = Elems<Expr>;
        using Places = list<Expr_place_ptr>;

        using value_type = Places::value_type;
        using iterator = Places::iterator;
        using const_iterator = Places::const_iterator;

        Expr();
        virtual ~Expr()                                             = default;
        virtual Expr_place_ptr clone() const override;
        Expr(const Expr& rhs);
        Expr& operator =(const Expr& rhs);
        Expr(Expr&& rhs)                                            = default;
        Expr& operator =(Expr&& rhs)                                = default;
        Expr(initializer_list<Expr_place_ptr> list);
        Expr(string input);
        Expr(istream& is);
        Expr(istream&& is);

        template <typename... Args>
            static Expr_ptr_t<Expr> new_expr(Args&&... args);

        virtual bool is_etoken() const noexcept override     { return false; }
        virtual explicit operator string () const noexcept override;

        const Places& cplaces() const                      { return _places; }
        size_t size() const noexcept              { return cplaces().size(); }
        bool empty() const noexcept                    { return size() == 0; }

        const Expr_place_ptr& cfront() const;
        const Expr_place_ptr& cback() const;
        Expr_place_ptr& front();
        Expr_place_ptr& back();
        const_iterator cbegin() const       { return std::cbegin(cplaces()); }
        const_iterator cend() const           { return std::cend(cplaces()); }
        const_iterator begin() const         { return std::begin(cplaces()); }
        const_iterator end() const             { return std::end(cplaces()); }
        iterator begin()                      { return std::begin(places()); }
        iterator end()                          { return std::end(places()); }

        bool valid_pos() const;
        void check_pos() const;
        void reset_pos();
        void maybe_reset_pos();
        void next() const;
        void prev() const;

        const Expr_place_ptr& cpeek() const;
        const Expr_place_ptr& cget() const;
        const Expr_place_ptr& cget_next() const;
        Expr_place_ptr& peek();
        Expr_place_ptr& get();
        Expr_place_ptr& get_next();

        const Expr_place_ptr& cpeek_check() const;
        const Expr_place_ptr& cget_check() const;
        Expr_place_ptr& peek_check();
        Expr_place_ptr& get_check();
        const Expr_place_ptr& cget_next_check() const;
        Expr_place_ptr& get_next_check();

        static const Expr_token&
            cptr_to_etoken(const Expr_place_ptr& place_ptr);
        static const Token&
            cptr_to_token(const Expr_place_ptr& place_ptr);
        static const Expr&
            cptr_to_expr(const Expr_place_ptr& place_ptr);
        static Expr_token& ptr_to_etoken(Expr_place_ptr& place_ptr);
        static Token& ptr_to_token(Expr_place_ptr& place_ptr);
        static Expr& ptr_to_expr(Expr_place_ptr& place_ptr);
        const Expr_token& cto_etoken(iterator it) const;
        const Token& cto_token(iterator it) const;
        const Expr& cto_expr(iterator it) const;
        Expr_token& to_etoken(iterator it);
        Token& to_token(iterator it);
        Expr& to_expr(iterator it);
        const Expr_token& cget_etoken() const;
        const Token& cget_token() const;
        const Expr& cget_expr() const;
        Expr_token& get_etoken();
        Token& get_token();
        Expr& get_expr();
        const Expr_token& cget_next_etoken() const;
        const Token& cget_next_token() const;
        const Expr& cget_next_expr() const;
        Expr_token& get_next_etoken();
        Token& get_next_token();
        Expr& get_next_expr();

        static void check_is_etoken(const Expr_place_ptr& place_ptr);
        static void check_is_expr(const Expr_place_ptr& place_ptr);
        static const Expr_token&
            cptr_to_etoken_check(const Expr_place_ptr& place_ptr);
        static const Token&
            cptr_to_token_check(const Expr_place_ptr& place_ptr);
        static const Expr&
            cptr_to_expr_check(const Expr_place_ptr& place_ptr);
        static Expr_token& ptr_to_etoken_check(Expr_place_ptr& place_ptr);
        static Token& ptr_to_token_check(Expr_place_ptr& place_ptr);
        static Expr& ptr_to_expr_check(Expr_place_ptr& place_ptr);
        const Expr_token& cto_etoken_check(iterator it) const;
        const Token& cto_token_check(iterator it) const;
        const Expr& cto_expr_check(iterator it) const;
        Expr_token& to_etoken_check(iterator it);
        Token& to_token_check(iterator it);
        Expr& to_expr_check(iterator it);
        const Expr_token& cget_etoken_check() const;
        const Token& cget_token_check() const;
        const Expr& cget_expr_check() const;
        Expr_token& get_etoken_check();
        Token& get_token_check();
        Expr& get_expr_check();
        const Expr_token& cget_next_etoken_check() const;
        const Token& cget_next_token_check() const;
        const Expr& cget_next_expr_check() const;
        Expr_token& get_next_etoken_check();
        Token& get_next_token_check();
        Expr& get_next_expr_check();

        template <typename T> void push_back(T&& place_ptr_);
        template <typename... Args> void emplace_back(Args&&... args);
        iterator erase(const_iterator pos);
        iterator erase(const_iterator first, const_iterator last);
        void resize(size_t size_);
        void clear();

        template <typename T> void add_place_ptr(T&& place_ptr_);
        template <typename... Args> void add_new_etoken(Args&&... args);
        template <typename... Args> void add_new_expr(Args&&... args);
        void erase_at_pos();
        void erase_from_pos(const_iterator last);

        template <typename Un_f> void for_each_expr(Un_f f);

        Expr& simplify() noexcept;
        Expr& to_binary();
        bool is_flat() const;
        bool is_deep() const;
        template <typename Arg> bool has_valid_values() const;
        template <typename Arg> void check_has_valid_values() const;
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
        Expr(istream& is, streampos& last_pos, unsigned depth);
        void parse(istream& is, streampos& last_pos, unsigned depth);

        Places& places()                                   { return _places; }

        iterator& pos() const;
        void invalidate_pos();
    private:
        Expr& simplify_top() noexcept;
        Expr& simplify_rec() noexcept;

        Places _places;
        bool _is_simplified{false};
        bool _is_binary{false};
        bool _is_flatten{false};

        mutable iterator _pos;
        mutable bool _valid_pos{false};
    };
}

#include "expr.tpp"
