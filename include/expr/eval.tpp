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
        // {"xor", [](Arg a, Arg b){ return !a ^ !b; }},
        {"=>",  [](Arg a, Arg b){ return !a || b; }},
    };

    template <typename Arg>
    template <typename Cont>
    Arg Expr::Eval<Arg>::call(Cont&& cont)
    {
        if (cont.size() != size()) {
            throw Error("Count of parameters mismatch: expected "s
                        + to_string(size())
                        + ", got " + to_string(cont.size()));
        }
        param_values() = forward<Cont>(cont);
        return (oper())();
    }

    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Params_link params_l, const Expr& expr)
        : _params_l(params_l)
    {
        if (expr.size() != 3) {
            throw Error("Expression is not binary.");
        }
        if (!expr.cfirst()->is_token()) {
            throw Error("First argument of expression must be token.");
        }
        const F_key key = static_cast<Expr_token&>(*expr.cfirst()).token();
        if (!bin_fs.includes(key)) {
            throw Error("First argument of expression "
                        "is not operation token: "s
                        + key);
        }
        _f = bin_fs[key];
        set_arg_fs(expr);
    }

    template <typename Arg>
    template <size_t idx>
    typename Expr::Eval<Arg>::Oper::Arg_f
        Expr::Eval<Arg>::Oper::get_arg_f(const Expr& expr)
    {
        const auto& place = expr[idx+1];
        if (!place->is_token()) {
            const auto& subexpr = static_cast<Expr&>(*place);
            Oper_ptr& oper_ptr = get<idx>(_oper_ptrs);
            oper_ptr = new_oper(Oper(_params_l, subexpr));
            return oper_f(oper_ptr);
        }
        const auto& token = static_cast<Expr_token&>(*place);
        Arg arg;
        if (token.value(arg)) {
            return arg_f(arg);
        }
        Param_key key = token.token();
        return param_f(key);
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys::iterator
        Expr::Eval<Arg>::Oper::set_param_key(const Param_key& key)
    {
        auto pos = find_param_key(key);
        if (pos != std::end(cparam_keys())) return pos;
        return param_keys().insert(pos, key);
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_f
        Expr::Eval<Arg>::Oper::param_f(const Param_key& key)
    {
        const Param_values& param_values_ = cparam_values();
        auto it = set_param_key(key);
        size_t idx = distance(std::begin(param_keys()), it);
        return [&param_values_, idx](){ return param_values_[idx]; };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_f
        Expr::Eval<Arg>::Oper::oper_f(const Oper_ptr& oper_ptr)
    {
        const Oper *const oper_link_ = oper_link(oper_ptr);
        return [oper_link_](){ return (*oper_link_)(); };
    }
}
