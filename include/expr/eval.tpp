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
    Expr::Eval<Arg>::Eval(const Exprs& exprs)
        : _oper(_params, exprs)
    {

    }

    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Params& params, const Exprs& exprs)
        // : _arg_refs{_args.first, _args.second}, _params(params)
        : _params(params)
    {
        if (exprs.size() != 3) {
            throw Error("Expression is not binary.");
        }
        if (!exprs.first()->is_token()) {
            throw Error("First argument of expression must be token.");
        }
        F_key key = "<NO_KEY>";
        try {
            key = static_cast<Token&>(*exprs.first()).token().data();
            _f = bin_fs[key];
        }
        catch (const std::out_of_range& e) {
            throw Error("First argument of expression is not operation token: "s
                        + key);
        }
        // set_arg(exprs, 0);
        // set_arg(exprs, 1);
        // set_arg_ptr(exprs, 0);
        // set_arg_ptr(exprs, 1);
        // _arg_ptrs.first = get_arg_ptr(exprs, 0);
        // _arg_ptrs.second = get_arg_ptr(exprs, 0);
        _arg_fs.first = get_arg_f(exprs, 0);
        _arg_fs.second = get_arg_f(exprs, 0);
    }

    template <typename Arg>
    // void Expr::Eval<Arg>::Oper::set_arg(const Exprs& exprs, size_t idx)
    // void Expr::Eval<Arg>::Oper::set_arg_ptr(const Exprs& exprs, size_t idx)
    // typename Expr::Eval<Arg>::Oper::Arg_ptr Expr::Eval<Arg>::Oper::get_arg_ptr(const Exprs& exprs, size_t idx)
    typename Expr::Eval<Arg>::Oper::Arg_f Expr::Eval<Arg>::Oper::get_arg_f(const Exprs& exprs, size_t idx)
    {
        // Arg& arg_ref = idx ? _args.second : _args.first;
        Arg& arg = idx ? _args.second : _args.first;
        // Arg_ptr& arg_ptr = idx ? _arg_ptrs.second : _arg_ptrs.first;
        auto& expr = exprs[idx+1];
        if (expr->is_token()) {
            auto& token = static_cast<Token&>(*expr);
            if (token.value(arg)) {
                // arg_ref = arg;
                // arg_ptr = &arg;
                return &arg;
            }
            else {
                Param_key key = token.token();
                add_param(key);
                // arg_ptr = param_ptr(key);
                return param_ptr(key);
            }
            // return;
        }
        auto& subexpr = static_cast<Exprs&>(*expr);
        Oper oper = Oper(_params, subexpr);
        // return &oper;
    }
}
