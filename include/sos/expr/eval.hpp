#pragma once

#include "sos.hpp"
#include "expr.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Param_key = Token;
        using Param_keys = vector<Param_key>;
        using Param_values = vector<Arg>;
        template <typename T> using Param_ptr_t = shared_ptr<T>;
        using Param_keys_ptr = Param_ptr_t<Param_keys>;
        using Param_values_ptr = Param_ptr_t<Param_values>;

        class Run;

        Eval()                                                      = default;
        ~Eval()                                                     = default;
        Eval(const Eval& rhs)                                       = default;
        Eval& operator =(const Eval& rhs)                           = default;
        Eval(Eval&& rhs)                                            = default;
        Eval& operator =(Eval&& rhs)                                = default;
        Eval(Expr expr,
             Param_keys_ptr param_keys_ptr_,
             Param_values_ptr param_values_ptr_ = new_param_values({}));
        Eval(Expr expr, Param_keys param_keys_ = {});
        Eval(string str, Param_keys param_keys_ = {})
                                : Eval(Expr(move(str)), move(param_keys_)) { }

        size_t size() const                   { return cparam_keys().size(); }

        static Param_keys_ptr
            new_param_keys(Param_keys&& param_keys_);
        static Param_values_ptr
            new_param_values(Param_values&& param_values_);
        const Param_keys_ptr& cparam_keys_ptr() const;
        Param_values_ptr& param_values_ptr() const;
        const Param_keys& cparam_keys() const;
        Param_values& param_values() const;

        Arg operator ()(initializer_list<Arg> list) const;
        Arg operator ()(Param_values param_values_) const;
        Arg operator ()(Param_values_ptr param_values_ptr_) const;
        Arg operator ()() const;

        explicit operator string () const;
        template <typename T> friend string to_string(const Eval<T>& rhs);
        template <typename T> friend ostream& operator <<(ostream& os,
                                                          const Eval<T>& rhs);
    protected:
        using Param_keys_link = Param_keys_ptr;
        using Param_values_link = Param_values_ptr;

        class Oper;
        using Oper_ptr = shared_ptr<Oper>;
        using Oper_link = Oper*;

        using Un_f = function<Arg(Arg)>;
        using Bin_f = function<Arg(Arg, Arg)>;
        using F_key = const string;
        template <typename F> using F_pair = pair<F_key, F>;
        template <typename F> using F_map =
            Const_map<typename F_pair<F>::first_type,
                      typename F_pair<F>::second_type>;
        static const F_map<Un_f> un_fs;
        static const F_map<Bin_f> bin_fs;

        Param_keys_ptr& param_keys_ptr();
        Param_keys& param_keys();
        Param_keys_link& param_keys_link();
        Param_values_link& param_values_link();

        static Oper_ptr new_oper(Oper&& oper_);
        const Oper& coper() const                            { return _oper; }
        Oper& oper()                                         { return _oper; }
        static Oper_link oper_link(const Oper_ptr& oper_ptr_);
    private:
        template <typename T> static T&& check_param_keys(T&& param_keys_);
        template <typename Cont> Cont&& check_param_values(Cont&& cont) const;
        Arg call() const                               { return (coper())(); }

        Param_keys_ptr _param_keys_ptr;
        mutable Param_values_ptr _param_values_ptr;
        Oper _oper;
        mutable bool _valid_values{false};
    };
}

#include "expr/eval.tpp"
