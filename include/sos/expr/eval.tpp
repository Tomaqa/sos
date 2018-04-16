#include "expr/eval/oper.hpp"

#include <cmath>

namespace SOS {
    template <typename Arg>
    const typename Expr::Eval<Arg>::template
        F_map<typename Expr::Eval<Arg>::Un_f> Expr::Eval<Arg>::un_fs{
        {"+",   [](Arg a){ return a; }},
        {"-",   [](Arg a){ return -a; }},
        {"not", [](Arg a){ return !a; }},
        {"abs", [](Arg a){ return abs(a); }},
        {"sqrt",[](Arg a){ return sqrt(a); }},
        {"cbrt",[](Arg a){ return cbrt(a); }},
        {"sin", [](Arg a){ return sin(a); }},
        {"cos", [](Arg a){ return cos(a); }},
        {"tan", [](Arg a){ return tan(a); }},
        {"exp", [](Arg a){ return exp(a); }},
        {"ln",  [](Arg a){ return log(a); }},
    };

    template <typename Arg>
    const typename Expr::Eval<Arg>::template
        F_map<typename Expr::Eval<Arg>::Bin_f> Expr::Eval<Arg>::bin_fs{
        {"+",   [](Arg a, Arg b){ return a + b; }},
        {"-",   [](Arg a, Arg b){ return a - b; }},
        {"*",   [](Arg a, Arg b){ return a * b; }},
        {"/",   [](Arg a, Arg b){ return a / b; }},
        {"^",   [](Arg a, Arg b){ return pow(a, b); }},
        {"=",   [](Arg a, Arg b){ return a == b; }},
        {"<",   [](Arg a, Arg b){ return a < b; }},
        {">",   [](Arg a, Arg b){ return a > b; }},
        {"<=",  [](Arg a, Arg b){ return a <= b; }},
        {">=",  [](Arg a, Arg b){ return a >= b; }},
        {"and", [](Arg a, Arg b){ return a && b; }},
        {"or",  [](Arg a, Arg b){ return a || b; }},
        {"=>",  [](Arg a, Arg b){ return !a || b; }},
    };

    template <typename Arg>
    Expr::Eval<Arg>::Eval(const Expr& expr_,
                          Param_keys_ptr param_keys_ptr_,
                          Param_values_ptr param_values_ptr_)
        : _param_keys_ptr(move(param_keys_ptr_)),
          _param_values_ptr(move(param_values_ptr_)),
          _oper(param_keys_link(), param_values_link(), expr_)
    { }

    template <typename Arg>
    Expr::Eval<Arg>::Eval(const Expr& expr_, Param_keys param_keys_)
        : Eval(expr_, new_param_keys(move(param_keys_)) )
    { }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys_ptr
        Expr::Eval<Arg>::new_param_keys(Param_keys&& param_keys_)
    {
        return make_shared<Param_keys>(
            move(check_param_keys(move(param_keys_)))
        );
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_values_ptr
        Expr::Eval<Arg>::new_param_values(Param_values&& param_values_)
    {
        // kontrola probiha az pri volani
        return make_shared<Param_values>(move(param_values_));
    }

    template <typename Arg>
    const typename Expr::Eval<Arg>::Param_keys_ptr&
        Expr::Eval<Arg>::cparam_keys_ptr() const
    {
        return _param_keys_ptr;
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys_ptr&
        Expr::Eval<Arg>::param_keys_ptr()
    {
        return _param_keys_ptr;
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_values_ptr&
        Expr::Eval<Arg>::param_values_ptr() const
    {
        return _param_values_ptr;
    }

    template <typename Arg>
    const typename Expr::Eval<Arg>::Param_keys&
        Expr::Eval<Arg>::cparam_keys() const
    {
        return *cparam_keys_ptr();
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys&
        Expr::Eval<Arg>::param_keys()
    {
        return *param_keys_ptr();
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_values&
        Expr::Eval<Arg>::param_values() const
    {
        return *param_values_ptr();
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys_link&
        Expr::Eval<Arg>::param_keys_link()
    {
        return param_keys_ptr();
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_values_link&
        Expr::Eval<Arg>::param_values_link()
    {
        return param_values_ptr();
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper_ptr Expr::Eval<Arg>::new_oper(Oper&& oper_)
    {
        return make_shared<Oper>(move(oper_));
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper_link
        Expr::Eval<Arg>::oper_link(const Oper_ptr& oper_ptr_)
    {
        return oper_ptr_.get();
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::operator ()(initializer_list<Arg> list) const
    {
        param_values() = move(check_param_values(move(list)));
        return call();
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::operator ()(Param_values param_values_) const
    {
        param_values() = move(check_param_values(move(param_values_)));
        return call();
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::operator ()(Param_values_ptr param_values_ptr_) const
    {
        check_param_values(*param_values_ptr_);
        param_values_ptr() = move(param_values_ptr_);
        return call();
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::operator ()() const
    {
        return call();
    }

    template <typename Arg>
    template <typename T>
    T&& Expr::Eval<Arg>::check_param_keys(T&& param_keys_)
    {
        // ! unieqness is not checked
        for_each(param_keys_, bind(&Expr_token::check_token, _1));
        return forward<T>(param_keys_);
    }

    template <typename Arg>
    template <typename Cont>
    Cont&& Expr::Eval<Arg>::check_param_values(Cont&& cont) const
    {
        expect(cont.size() == size(),
               "Count of parameters mismatch: expected "s + to_string(size())
               + ", got " + to_string(cont.size()));
        _valid_values = true;
        return forward<Cont>(cont);
    }

    template <typename Arg>
    Expr::Eval<Arg>::operator string () const
    {
        string str = "[ "s + to_string(cparam_keys()) + "]";
        if (_valid_values) str += " <-- [ " + to_string(param_values()) + "]";
        return move(str);
    }

    template <typename Arg>
    string to_string(const Expr::Eval<Arg>& rhs)
    {
        return move((string)rhs);
    }

    template <typename Arg>
    ostream& operator <<(ostream& os, const Expr::Eval<Arg>& rhs)
    {
        return (os << to_string(rhs));
    }
}
