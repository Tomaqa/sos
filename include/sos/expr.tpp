#include <sstream>

namespace SOS {
    ///////////////////////////////////////////////////////////////

    template <typename Arg>
    bool Expr_token::get_value_check(Arg& arg) const
    {
        istringstream iss(_token);
        return (bool)(iss >> arg);
    }

    template <typename Arg>
    Arg Expr_token::get_value() const
    {
        Arg arg;
        get_value_check(arg);
        return arg;
    }

    template <typename Arg>
    bool Expr_token::is_value() const
    {
        Arg v;
        return get_value_check(v);
    }

    ///////////////////////////////////////////////////////////////

    template <typename Un_f>
    void Expr::for_each_expr(Un_f f)
    {
        for (auto& eptr : *this) {
            if (eptr->is_etoken()) continue;
            Expr& subexpr = ptr_to_expr(eptr);
            f(subexpr);
        }
    }

    template <typename Arg>
    bool Expr::has_values() const
    {
        if (!is_flat()) return false;
        return std::all_of(cbegin(), cend(),
                           bind(&Expr_token::is_value<Arg>,
                                bind(&Expr::cptr_to_etoken, _1))
                           );
    }

    template <typename Arg>
    Expr::Elems<Arg> Expr::transform_to_args() const
    {
        expect(has_values<Arg>(), "Elements are not of demanded type.");
        Elems<Arg> elems;
        elems.reserve(size());
        std::transform(cbegin(), cend(),
                       std::back_inserter(elems),
                       bind(&Expr_token::get_value<Arg>,
                            bind(&Expr::cptr_to_etoken, _1))
                       );
        return move(elems);
    }

    template <typename Arg>
    Expr::Eval<Arg> Expr::get_eval(typename Eval<Arg>::Param_keys param_keys_)
    {
        return {to_binary(), move(param_keys_)};
    }

    template <typename Arg>
    Expr::Eval<Arg>
        Expr::get_eval(typename Eval<Arg>::Param_keys_ptr param_keys_ptr_)
    {
        return {to_binary(), move(param_keys_ptr_)};

    }

    template <typename Arg>
    Expr::Eval<Arg>
        Expr::get_eval(typename Eval<Arg>::Param_keys_ptr param_keys_ptr_,
                       typename Eval<Arg>::Param_values_ptr
                           param_values_ptr_)
    {
        return {to_binary(), move(param_keys_ptr_), move(param_values_ptr_)};
    }
}
