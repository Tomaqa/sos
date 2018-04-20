#pragma once

#include "sos.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        Oper()                                                      = default;
        ~Oper()                                                     = default;
        Oper(const Oper& rhs)                                       = default;
        Oper& operator =(const Oper& rhs)                           = default;
        Oper(Oper&& rhs)                                            = default;
        Oper& operator =(Oper&& rhs)                                = default;
        Oper(Param_keys_link& param_keys_l_,
             Param_values_link& param_values_l_,
             Expr&& expr);

        size_t size() const                    { return param_keys().size(); }
        const Param_keys_link& cparam_keys_link() const;
        const Param_values_link& cparam_values_link() const;
        Param_keys& param_keys() const;
        const Param_values& cparam_values() const;

        Arg operator ()() const;
    protected:
        using Arg_lazy = Lazy<Arg>;
        using Args_lazy = pair<Arg_lazy, Arg_lazy>;
        using Oper_ptrs = pair<Oper_ptr, Oper_ptr>;

        using iterator = Param_keys::iterator;

        iterator find_param_key(const Param_key& key_) const;
        iterator set_param_key(Param_key key_) const;
    private:
        bool is_binary() const                          { return _is_binary; }

        void set_lazy_args(Expr& expr);
        template <int idx> void set_lazy_arg(Expr& expr);
        template <int idx> Arg_lazy get_arg_lazy(Expr_place_ptr& place);

        Arg_lazy arg_lazy(Arg arg) const noexcept;
        Arg_lazy param_lazy(Param_key key_) const;
        Arg_lazy oper_lazy(const Oper_ptr& oper_ptr_) const;

        //! potentionally inefficient
        //!   - operations are not stored in continual memory blocks
        //!   - binary operations -> maximal depth
        //!   - if both arguments are known, whole operation can be simplified
        Param_keys_link _param_keys_l;
        Param_values_link _param_values_l;
        Un_f _un_f;
        Bin_f _bin_f;
        bool _is_binary;
        Args_lazy _args_lazy;
        Oper_ptrs _oper_ptrs;
    };
}

#include "expr/eval/oper.tpp"
