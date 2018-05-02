#include <sstream>

#include <iostream>
#include <iomanip>

namespace SOS {
    template <typename T>
    Expr_place::Expr_ptr_t<T> Expr_place::new_place(T&& place)
    {
        return make_unique<T>(forward<T>(place));
    }

    ///////////////////////////////////////////////////////////////

    template <typename Arg>
    Expr_value<Arg>::Expr_value(Arg arg)
        : _value(move(arg))
    { }

    template <typename Arg>
    Expr_place::Expr_place_ptr Expr_value<Arg>::clone() const
    {
        return new_evalue(*this);
    }

    template <typename Arg>
    Expr_place::Expr_place_ptr Expr_value<Arg>::move_to_ptr()
    {
        return new_evalue(move(*this));
    }

    template <typename Arg>
    template <typename... Args>
    Expr_place::Expr_ptr_t<Expr_value<Arg>>
        Expr_value<Arg>::new_evalue(Args&&... args)
    {
        return new_place(Expr_value<Arg>(forward<Args>(args)...));
    }

    template <typename Arg>
    Expr_value<Arg>::operator string () const noexcept
    {
        return to_string(cvalue());
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
        istringstream iss(ctoken());
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
               "Token value is not of demanded type: '"s
               + ctoken() + "'");
        return arg;
    }

    template <typename Arg>
    bool Expr_token::is_valid_value() const
    {
        Arg v;
        return get_value_valid(v);
    }

    template <typename Arg>
    void Expr_token::set_value(Arg arg)
    {
        token() = move(to_string(move(arg)));
    }

    ///////////////////////////////////////////////////////////////

    template <typename... Args>
    Expr_place::Expr_ptr_t<Expr> Expr::new_expr(Args&&... args)
    {
        return new_place(Expr(forward<Args>(args)...));
    }

    template <typename Arg>
    const Expr_value<Arg>&
        Expr::cptr_to_evalue(const Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_value<Arg>&>(*place_ptr);
    }

    template <typename Arg>
    Expr_value<Arg>& Expr::ptr_to_evalue(Expr_place_ptr& place_ptr)
    {
        return static_cast<Expr_value<Arg>&>(*place_ptr);
    }

    template <typename Arg>
    Arg Expr::cptr_to_value(const Expr_place_ptr& place_ptr)
    {
        if (is_expr(place_ptr)) {
            return cptr_to_expr(place_ptr).get_eval<Arg>()();
        }
        if (is_evalue(place_ptr)) {
            return cptr_to_evalue<Arg>(place_ptr).cvalue();
        }
        return cptr_to_etoken(place_ptr).get_value<Arg>();
    }

    template <typename Arg>
    Arg Expr::ptr_to_value(Expr_place_ptr& place_ptr)
    {
        if (is_expr(place_ptr)) {
            return ptr_to_expr(place_ptr).get_eval<Arg>()();
        }
        if (is_evalue(place_ptr)) {
            return ptr_to_evalue<Arg>(place_ptr).cvalue();
        }
        return ptr_to_etoken(place_ptr).get_value<Arg>();
    }

    template <typename Arg>
    Arg Expr::cpeek_value() const
    {
        return cptr_to_value<Arg>(cpeek());
    }

    template <typename Arg>
    Arg Expr::get_value()
    {
        return ptr_to_value<Arg>(get());
    }

    template <typename Arg>
    Arg Expr::extract_value()
    {
        return ptr_to_value<Arg>(extract());
    }

    template <typename Arg>
    Arg Expr::cptr_to_value_check(const Expr_place_ptr& place_ptr)
    {
        if (is_expr(place_ptr)) {
            return cptr_to_expr(place_ptr).get_eval<Arg>()();
        }
        if (is_evalue(place_ptr)) {
            return cptr_to_evalue<Arg>(place_ptr).cvalue();
        }
        return cptr_to_etoken(place_ptr).get_value_check<Arg>();
    }

    template <typename Arg>
    Arg Expr::ptr_to_value_check(Expr_place_ptr& place_ptr)
    {
        if (is_expr(place_ptr)) {
            return ptr_to_expr(place_ptr).get_eval<Arg>()();
        }
        if (is_evalue(place_ptr)) {
            return ptr_to_evalue<Arg>(place_ptr).cvalue();
        }
        return ptr_to_etoken(place_ptr).get_value_check<Arg>();
    }

    template <typename Arg>
    Arg Expr::cpeek_value_check() const
    {
        return cptr_to_value_check<Arg>(cpeek());
    }

    template <typename Arg>
    Arg Expr::get_value_check()
    {
        return ptr_to_value_check<Arg>(get());
    }

    template <typename Arg>
    Arg Expr::extract_value_check()
    {
        return ptr_to_value_check<Arg>(extract());
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
    Expr::iterator Expr::insert(const_iterator pos, T&& place_ptr_)
    {
        return emplace(pos, forward<T>(place_ptr_));
    }

    template <typename... Args>
    Expr::iterator Expr::emplace(const_iterator pos, Args&&... args)
    {
        return places().emplace(pos, forward<Args>(args)...);
    }

    template <typename T>
    void Expr::add_place_ptr(T&& place_ptr_)
    {
        emplace_back(forward<T>(place_ptr_));
    }

    template <typename Arg, typename... Args>
    void Expr::add_new_evalue(Args&&... args)
    {
        add_place_ptr(Expr_value<Arg>::new_evalue(forward<Args>(args)...));
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

    template <typename T>
    Expr::iterator Expr::add_place_ptr_at_pos(T&& place_ptr_)
    {
        return emplace(cpos(), forward<T>(place_ptr_));
    }

    template <typename Arg, typename... Args>
    Expr::iterator Expr::add_new_evalue_at_pos(Args&&... args)
    {
        return add_place_ptr_at_pos(
            Expr_value<Arg>::new_evalue(forward<Args>(args)...)
        );
    }

    template <typename... Args>
    Expr::iterator Expr::add_new_etoken_at_pos(Args&&... args)
    {
        return add_place_ptr_at_pos(
            Expr_token::new_etoken(forward<Args>(args)...)
        );
    }

    template <typename... Args>
    Expr::iterator Expr::add_new_expr_at_pos(Args&&... args)
    {
        return add_place_ptr_at_pos(
            new_expr(forward<Args>(args)...)
        );
    }

    template <typename Un_f>
    void Expr::for_each_expr(Un_f f)
    {
        for (auto& eptr : *this) {
            if (!is_expr(eptr)) continue;
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
