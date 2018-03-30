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
    Arg Expr::Eval<Arg>::operator () (initializer_list<Arg> list)
    {
        if (list.size() != size()) {
            throw Error("Count of parameters mismatch: expected "s
                        + to_string(size())
                        + ", got " + to_string(list.size()));
        }
        param_values() = list;
        return (oper())();
    }

    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Params_link params_l, const Exprs& exprs)
        : _params_l(params_l)
    {
        if (exprs.size() != 3) {
            throw Error("Expression is not binary.");
        }
        if (!exprs.first()->is_token()) {
            throw Error("First argument of expression must be token.");
        }
        const F_key key = static_cast<Token&>(*exprs.first()).token();
        if (!bin_fs.includes(key)) {
            throw Error("First argument of expression "
                        "is not operation token: "s
                        + key);
        }
        _f = bin_fs[key];
        set_arg_fs(exprs);
    }

    template <typename Arg>
    template <size_t idx>
    typename Expr::Eval<Arg>::Oper::Arg_f
        Expr::Eval<Arg>::Oper::get_arg_f(const Exprs& exprs)
    {
        const auto& expr = exprs[idx+1];
        if (!expr->is_token()) {
            const auto& subexprs = static_cast<Exprs&>(*expr);
            Oper_ptr& oper_ptr = get<idx>(_oper_ptrs);
            oper_ptr = new_oper(Oper(_params_l, subexprs));
            // return oper_f(*oper_ptr);
            return oper_f(oper_ptr.get());
        }
        const auto& token = static_cast<Token&>(*expr);
        Arg arg;
        if (token.value(arg)) {
            return arg_f(arg);
        }
        Param_key key = token.token();
        auto it = set_param_key(key);
        return param_f(param_values(), distance(begin(param_keys()), it));
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Param_keys::iterator
        Expr::Eval<Arg>::Oper::set_param_key(const Param_key& key)
    {
        auto pos = find_param_key(key);
        if (pos != end(param_keys())) return pos;
        return param_keys().insert(pos, key);
    }
}
