namespace SOS {
    template <typename Arg>
    Expr::Eval<Arg>::Oper::Oper(Param_keys_link& param_keys_l_,
                                Param_values_link& param_values_l_,
                                Expr&& expr_)
        : _param_keys_l(param_keys_l_), _param_values_l(param_values_l_)
    {
        const int size_ = expr_.size();
        expect(size_ == 2 || size_ == 3,
               "Expression is not unary nor binary.");
        F_key key_ = move(expr_.cto_token_check(0));
        _is_binary = (size_ == 3);
        if (is_binary()) {
            expect(bin_fs.includes(key_),
                   "First argument of binary expression "s
                   + "is not binary operation token: "s
                   + key_);
            _bin_f = bin_fs[key_];
        }
        else {
            expect(un_fs.includes(key_),
                   "First argument of unary expression "s
                   + "is not unary operation token: "s
                   + key_);
            _un_f = un_fs[key_];
        }
        set_lazy_args(expr_);
    }

    template <typename Arg>
    void Expr::Eval<Arg>::Oper::set_lazy_args(Expr& expr_)
    {
        set_lazy_arg<0>(expr_);
        if (is_binary()) set_lazy_arg<1>(expr_);
    }

    template <typename Arg>
    template <int idx>
    void Expr::Eval<Arg>::Oper::set_lazy_arg(Expr& expr_)
    {
        get<idx>(_args_lazy) = move(get_arg_lazy<idx>(expr_));
    }

    template <typename Arg>
    template <int idx>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::get_arg_lazy(Expr& expr_)
    {
        auto&& place_ = move(expr_[idx+1]);
        if (!place_->is_etoken()) {
            auto&& subexpr = move(ptr_to_expr(place_));
            Oper_ptr& oper_ptr_ = get<idx>(_oper_ptrs);
            oper_ptr_ = new_oper(Oper(_param_keys_l, _param_values_l,
                                      move(subexpr)));
            return oper_lazy(oper_ptr_);
        }
        auto&& token_ = move(ptr_to_etoken(place_));
        Arg arg;
        if (token_.get_value_check(arg)) {
            return arg_lazy(arg);
        }
        Param_key&& key_ = move(token_.token());
        return param_lazy(move(key_));
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
        if (is_binary()) return _bin_f((_args_lazy.first)(),
                                       (_args_lazy.second)());
        return _un_f((_args_lazy.first)());
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
        Expr::Eval<Arg>::Oper::set_param_key(Param_key key_) const
    {
        auto pos = find_param_key(key_);
        if (pos != std::end(param_keys())) return pos;
        return param_keys().emplace(pos, move(key_));
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::arg_lazy(Arg arg) const noexcept
    {
        return [arg](){ return arg; };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::param_lazy(Param_key key_) const
    {
        auto it = set_param_key(move(key_));
        int idx = std::distance(std::begin(param_keys()), it);
        return [params_l = &cparam_values(), idx](){
            return (*params_l)[idx];
        };
    }

    template <typename Arg>
    typename Expr::Eval<Arg>::Oper::Arg_lazy
        Expr::Eval<Arg>::Oper::oper_lazy(const Oper_ptr& oper_ptr_) const
    {
        return [op_l = oper_link(oper_ptr_)](){
            return (*op_l)();
        };
    }
}
