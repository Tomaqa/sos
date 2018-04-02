namespace SOS {
    template <typename Arg>
    const typename Expr::Eval<Arg>::template
        F_map<typename Expr::Eval<Arg>::Bin_f> Expr::Eval<Arg>::bin_fs {
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
    template <typename Cont>
    Arg Expr::Eval<Arg>::call(Cont&& cont) const
    {
        expect(cont.size() == size(),
               "Count of parameters mismatch: expected "s + to_string(size())
               + ", got " + to_string(cont.size()));
        param_values() = forward<Cont>(cont);
        return (coper())();
    }

    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Param_keys_link param_keys_l_,
                                Param_values_link param_values_l_,
                                const Expr& expr_)
        : _param_keys_l(param_keys_l_), _param_values_l(param_values_l_)
    {
        expect(expr_.size() == 3, "Expression is not binary.");
        expect(expr_.cfront()->is_token(),
               "First argument of expression must be token.");
        const F_key key_ = expr_.cto_token(0).token();
        expect(bin_fs.includes(key_),
               "First argument of expression is not operation token: "s + key_);
        _f = bin_fs[key_];
        set_lazy_args(expr_);
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
            oper_ptr_ = new_oper(Oper(_param_keys_l, _param_values_l, subexpr));
            return oper_lazy(oper_ptr_);
        }
        const auto& token_ = cptr_to_token(place_);
        Arg arg;
        if (token_.get_value_check(arg)) {
            return arg_lazy(arg);
        }
        Param_key key_ = token_.token();
        return param_lazy(key_);
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
        Expr::Eval<Arg>::Oper::param_lazy(const Param_key& key_) const
    {
        const Param_values& param_values_ = param_values();
        auto it = set_param_key(key_);
        int idx = distance(std::begin(param_keys()), it);
        return [&param_values_, idx](){ return param_values_[idx]; };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::oper_lazy(const Oper_ptr& oper_ptr_) const
    {
        const Oper *const oper_link_ = oper_link(oper_ptr_);
        return [oper_link_](){ return (*oper_link_)(); };
    }
}
