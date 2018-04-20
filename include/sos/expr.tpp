#include <sstream>

#include <iostream>

namespace SOS {
    template <typename T>
    Expr_place::Expr_ptr_t<T> Expr_place::new_place(T&& place)
    {
        return make_unique<T>(forward<T>(place));
    }

    ///////////////////////////////////////////////////////////////

    template <typename... Args>
    Expr_place::Expr_ptr_t<Expr_token> Expr_token::new_etoken(Args&&... args)
    {
        return new_place(Expr_token(forward<Args>(args)...));
    }

    template <typename Arg>
    bool Expr_token::get_value_valid(Arg& arg) const
    {
        istringstream iss(_token);
        return (bool)(iss >> arg);
    }

    template <typename Arg>
    Arg Expr_token::get_value() const
    {
        Arg arg;
        get_value_valid(arg);
        return arg;
    }

    template <typename Arg>
    Arg Expr_token::get_value_check() const
    {
        Arg arg;
        expect(get_value_valid(arg),
               "Token value is not  of demanded type: '"s
               + ctoken() + "'");
        return arg;
    }

    template <typename Arg>
    bool Expr_token::is_valid_value() const
    {
        Arg v;
        return get_value_valid(v);
    }

    ///////////////////////////////////////////////////////////////

    template <typename... Args>
    Expr_place::Expr_ptr_t<Expr> Expr::new_expr(Args&&... args)
    {
        return new_place(Expr(forward<Args>(args)...));
    }

    template <typename T>
    void Expr::push_back(T&& place_ptr_)
    {
        emplace_back(forward<T>(place_ptr_));
    }

    template <typename... Args>
    void Expr::emplace_back(Args&&... args)
    {
        places().emplace_back(forward<Args>(args)...);
        maybe_reset_pos();
    }

    template <typename T>
    void Expr::add_place_ptr(T&& place_ptr_)
    {
        emplace_back(forward<T>(place_ptr_));
    }

    template <typename... Args>
    void Expr::add_new_etoken(Args&&... args)
    {
        add_place_ptr(Expr_token::new_etoken(forward<Args>(args)...));
    }

    template <typename... Args>
    void Expr::add_new_expr(Args&&... args)
    {
        add_place_ptr(new_expr(forward<Args>(args)...));
    }

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
    bool Expr::has_valid_values() const
    {
        if (!is_flat()) return false;
        return std::all_of(cbegin(), cend(),
                           bind(&Expr_token::is_valid_value<Arg>,
                                bind(&Expr::cptr_to_etoken, _1))
                           );
    }

    template <typename Arg>
    void Expr::check_has_valid_values() const
    {
        expect(has_valid_values<Arg>(),
               "Elements are not of demanded type.");
    }

    template <typename Arg>
    Expr::Elems<Arg> Expr::transform_to_args() const
    {
        check_has_valid_values<Arg>();
        Elems<Arg> elems;
        elems.reserve(size());
        std::transform(cbegin(), cend(),
                       std::back_inserter(elems),
                       bind(&Expr_token::get_value<Arg>,
                            bind(&Expr::cptr_to_etoken, _1))
                       );
        return elems;
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
