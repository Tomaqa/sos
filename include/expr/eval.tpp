namespace SOS {
    template <typename Arg>
    const typename Expr::Eval<Arg>::template
        F_map<typename Expr::Eval<Arg>::Bin_f> Expr::Eval<Arg>::bin_fs{
        {"+",   [](Arg a, Arg b){ return a + b; }},
        {"-",   [](Arg a, Arg b){ return a - b; }},
        {"*",   [](Arg a, Arg b){ return a * b; }},
        {"/",   [](Arg a, Arg b){ return a / b; }},
        {"=",   [](Arg a, Arg b){ return a == b; }},
        {"<",   [](Arg a, Arg b){ return a < b; }},
        {">",   [](Arg a, Arg b){ return a > b; }},
        {"<=",  [](Arg a, Arg b){ return a <= b; }},
        {">=",  [](Arg a, Arg b){ return a >= b; }},
        {"not", [](Arg a, Arg b){ return !b; }},
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
    template <typename T>
    T&& Expr::Eval<Arg>::check_param_keys(T&& param_keys_)
    {
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

    ///////////////////////////////////////////////////////////////

    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Param_keys_link& param_keys_l_,
                                Param_values_link& param_values_l_,
                                const Expr& expr_)
        : _param_keys_l(param_keys_l_), _param_values_l(param_values_l_)
    {
        expect(expr_.size() == 3, "Expression is not binary.");
        expect(expr_.cfront()->is_token(),
               "First argument of expression must be token.");
        const F_key key_ = expr_.cto_token(0).ctoken();
        expect(bin_fs.includes(key_),
               "First argument of expression is not operation token: "s
               + key_);
        _f = bin_fs[key_];
        set_lazy_args(expr_);
    }

    template <typename Arg>
    void Expr::Eval<Arg>::Oper::set_lazy_args(const Expr& expr_)
    {
        set_lazy_arg<0>(expr_);
        set_lazy_arg<1>(expr_);
    }

    template <typename Arg>
    template <int idx>
    void Expr::Eval<Arg>::Oper::set_lazy_arg(const Expr& expr_)
    {
        get<idx>(_args_lazy) = get_arg_lazy<idx>(expr_);
    }

    template <typename Arg>
    template <int idx>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::get_arg_lazy(const Expr& expr_)
    {
        const auto& place_ = expr_[idx+1];
        if (!place_->is_token()) {
            const auto& subexpr = cptr_to_expr(place_);
            Oper_ptr& oper_ptr_ = get<idx>(_oper_ptrs);
            oper_ptr_ = new_oper(Oper(_param_keys_l, _param_values_l,
                                      subexpr));
            return oper_lazy(oper_ptr_);
        }
        const auto& token_ = cptr_to_token(place_);
        Arg arg;
        if (token_.get_value_check(arg)) {
            return arg_lazy(arg);
        }
        const Param_key& key_ = token_.ctoken();
        return param_lazy(key_);
    }

    template <typename Arg>
    const typename Expr::Eval<Arg>::Param_keys_ptr&
        Expr::Eval<Arg>::Oper::cparam_keys_link() const
    {
        return _param_keys_l;
    }

    template <typename Arg>
    const typename Expr::Eval<Arg>::Param_values_ptr&
        Expr::Eval<Arg>::Oper::cparam_values_link() const
    {
        return _param_values_l;
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys&
        Expr::Eval<Arg>::Oper::param_keys() const
    {
        return *cparam_keys_link();
    }

    template <typename Arg>
    const typename Expr::Eval<Arg>::Param_values&
        Expr::Eval<Arg>::Oper::cparam_values() const
    {
        return *cparam_values_link();
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::Oper::operator ()() const
    {
        return _f((_args_lazy.first)(),
                  (_args_lazy.second)());
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys::iterator
        Expr::Eval<Arg>::Oper::find_param_key(const Param_key& key_) const
    {
        return std::find(std::begin(param_keys()),
                         std::end(param_keys()), key_);
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys::iterator
        Expr::Eval<Arg>::Oper::set_param_key(const Param_key& key_) const
    {
        auto pos = find_param_key(key_);
        if (pos != std::end(param_keys())) return pos;
        return param_keys().insert(pos, key_);
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::arg_lazy(Arg arg) const noexcept
    {
        return [arg](){ return arg; };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::param_lazy(const Param_key& key_) const
    {
        auto it = set_param_key(key_);
        int idx = std::distance(std::begin(param_keys()), it);
        return [params_l = &cparam_values(), idx](){
            return (*params_l)[idx];
        };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::oper_lazy(const Oper_ptr& oper_ptr_) const
    {
        return [op_l = oper_link(oper_ptr_)](){ return (*op_l)(); };
    }
}
