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
    typename Expr::Eval<Arg>::Param_keys Expr::Eval<Arg>::param_keys() const
    {
        // Param_keys param_keys;
        // param_keys.reserve(size());
        // for (const auto& pair : _params) {
        //     param_keys.emplace_back(pair.first);
        // }
        // return move(param_keys);
        return _params.first;
    }

    template <typename Arg>
    Arg Expr::Eval<Arg>::operator () (initializer_list<Arg> list)
    {
        if (list.size() != size()) {
            throw Error("Count of parameters mismatch: expected "s
                        + to_string(size())
                        + ", got " + to_string(list.size()));
        }
        // for_each(_params.begin(), _params.end(),
            // [](const auto& pair){
                // set_param_value(pair.first, );
            // });
        // for_each(_params.begin(), _params.end(),
        _params.second = list;
        return _oper();
    }

    // template <typename Arg>
    // bool Expr::Eval<Arg>::set_param_value(const Param_key& key, Arg value)
    // {
    //     // if (!_params.count(key)) return false;
    //     // _params[key] = value;
    //     if (!_params->count(key)) return false;
    //     _params[key] = value;
    //     return true;
    // }

    template <typename Arg>
    // Expr::Eval<Arg>::Oper::Oper(Params& params, const Exprs& exprs)
        // : _params(params)
    Expr::Eval<Arg>::Oper::Oper(Params_ptr params_ptr, const Exprs& exprs)
        : _params_ptr(params_ptr)
    {
        if (exprs.size() != 3) {
            throw Error("Expression is not binary.");
        }
        if (!exprs.first()->is_token()) {
            throw Error("First argument of expression must be token.");
        }
        // F_key key = "<NO_KEY>";
        // try {
            // key = static_cast<Token&>(*exprs.first()).token().data();
            // const F_key key = static_cast<Token&>(*exprs.first()).token().data();
            const F_key key = static_cast<Token&>(*exprs.first()).token();
            if (!bin_fs.includes(key)) {
                throw Error("First argument of expression "
                            "is not operation token: "s
                            + key);
            }
            _f = bin_fs[key];
        // }
        // catch (const std::out_of_range& e) {
        //     cout << e.what() << endl;
        //     throw Error("First argument of expression "
        //                 "is not operation token: "s
        //                 // + key);
        //                 );
        // }
        // _arg_fs.first = get_arg_f(exprs, 0);
        // _arg_fs.second = get_arg_f(exprs, 1);
        _arg_fs.first = get_arg_f(exprs[1]);
        _arg_fs.second = get_arg_f(exprs[2]);
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_f
        // Expr::Eval<Arg>::Oper::get_arg_f(const Exprs& exprs, size_t idx)
        Expr::Eval<Arg>::Oper::get_arg_f(const Expr_ptr& expr)
    {
        // const auto& expr = exprs[idx+1];
        if (expr->is_token()) {
            const auto& token = static_cast<Token&>(*expr);
            Arg arg;
            if (token.value(arg)) {
                return [arg](){ return arg; };
            }
            Param_key key = token.token();
            cout << ">>>>" << key << endl;
            set_param_key(key);
            return param_f(key);
        }
        const auto& subexpr = static_cast<Exprs&>(*expr);
        // Oper oper = Oper(_params, subexpr);
        // Oper oper = Oper(_params_ptr, subexpr);
        // return [oper](){ return oper(); };
        return [this, &subexpr](){ return Oper(_params_ptr, subexpr)(); };
    }

    template <typename Arg>
    void Expr::Eval<Arg>::Oper::set_param_key(const Param_key& key)
    {
        // _params[key];
        // if (find_param_key(key) == end(_params.first)) {
            // _params.first.emplace_back(key);
        // if (find_param_key(key) == end(_params_ptr->first)) {
        if (find_param_key(key) == end(param_keys())) {
            // _params_ptr->first.emplace_back(key);
            // _params_ptr->first.push_back(Param_key(key));
            // param_keys().push_back(Param_key(key));
            param_keys().push_back(key);
        }
    }

    template <typename Arg>
    // const Arg& Expr::Eval<Arg>::Oper::param_value(const Param_key& key) const
    const Arg& Expr::Eval<Arg>::Oper::param_value(const Param_key& key)
    {
        // return _params.at(key);
        // _params.second.reserve(size());
        // auto idx = distance(cbegin(_params.first), c_find_param_key(key));
        // return _params.second[idx];
        // _params_ptr->second.reserve(size());
        param_values().reserve(size());
        cout << "POHODA?" << endl;
        // auto idx = distance(cbegin(_params_ptr->first), c_find_param_key(key));
        // auto idx = distance(_params_ptr->first.cbegin(), c_find_param_key(key));
        // auto idx = distance(begin(_params_ptr->first), find_param_key(key));
        // auto beg = begin(_params_ptr->first);
        cout << "finding: " << key << endl;
        auto beg = begin(param_keys());
        cout << "begin: " << *beg << endl;
        auto pos = find_param_key(key);
        cout << "found: " << *pos << endl;
        auto idx = distance(beg, pos);
        cout << "idx: " << idx << endl;
        cout << "PORAD POHODA?" << endl;
        // return _params_ptr->second[idx];
        return param_values()[idx];
    }
}
