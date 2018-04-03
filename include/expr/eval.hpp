#ifndef ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
#define ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430

#include "expr.hpp"

// ! <numeric> accumulate

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Param_key = Token;
        using Param_keys = vector<Param_key>;
        using Param_values = vector<Arg>;
        template <typename T>
        using Param_ptr_t = shared_ptr<T>;
        using Param_keys_ptr = Param_ptr_t<Param_keys>;
        using Param_values_ptr = Param_ptr_t<Param_values>;

        Eval() = default;
        ~Eval() = default;
        Eval(const Eval& rhs) = default;
        Eval& operator =(const Eval& rhs) = default;
        Eval(Eval&& rhs) = default;
        Eval& operator =(Eval&& rhs) = default;
        Eval(const Expr& expr_,
             Param_keys_ptr param_keys_ptr_,
             Param_values_ptr param_values_ptr_ = new_param_values({}))
            : _param_keys_ptr(move(param_keys_ptr_)),
              _param_values_ptr(move(param_values_ptr_)),
              _oper(param_keys_link(), param_values_link(), expr_) { }
        Eval(const Expr& expr_, Param_keys param_keys_ = {})
            : Eval(expr_, new_param_keys({check_keys(move(param_keys_))})) { }
        Eval(const string& str, Param_keys param_keys_ = {})
            : Eval(Expr(str), move(param_keys_)) { }

        size_t size() const
            { return cparam_keys().size(); }
        const Param_keys& cparam_keys() const
            { return *_param_keys_ptr; }
        Param_values& param_values() const
            { return *_param_values_ptr; }
        const Param_keys_ptr& cparam_keys_ptr() const
            { return _param_keys_ptr; }
        Param_values_ptr& param_values_ptr() const
            { return _param_values_ptr; }

        Arg operator ()(initializer_list<Arg> list) const;
        Arg operator ()(Param_values param_values_) const;
        Arg operator ()(Param_values_ptr param_values_ptr_) const;

        explicit operator string () const;
        friend string to_string(const Eval& rhs)
            { return move((string)rhs); }
        friend ostream& operator <<(ostream& os, const Eval& rhs)
            { return (os << to_string(rhs)); }
    protected:
        class Oper;
        using Oper_ptr = shared_ptr<Oper>;

        using Bin_f = function<Arg(Arg, Arg)>;
        using F_key = const string;
        template <typename F>
        using F_pair = pair<F_key, F>;
        template <typename F>
        using F_map = Const_map<typename F_pair<F>::first_type,
                                typename F_pair<F>::second_type>;
        static const F_map<Bin_f> bin_fs;

        static Param_keys_ptr new_param_keys(Param_keys&& param_keys_)
            { return make_shared<Param_keys>(move(param_keys_)); }
        static Param_values_ptr new_param_values(Param_values&& param_values_)
            { return make_shared<Param_values>(move(param_values_)); }
        Param_keys* param_keys_link()
            { return _param_keys_ptr.get(); }
        Param_values* param_values_link()
            { return _param_values_ptr.get(); }
        Param_keys& param_keys()
            { return *_param_keys_ptr; }
        const Oper& coper() const { return _oper; }
        Oper& oper() { return _oper; }
        static Param_keys&& check_keys(Param_keys&& param_keys_);

        static Oper_ptr new_oper(Oper&& oper_)
            { return make_shared<Oper>(move(oper_)); }
        static Oper* oper_link(const Oper_ptr& oper_ptr_)
            { return oper_ptr_.get(); }
    private:
        template <typename Cont>
        void check_param_values(Cont&& cont) const;
        Arg call() const
            { return (coper())(); }

        Param_keys_ptr _param_keys_ptr;
        mutable Param_values_ptr _param_values_ptr;
        Oper _oper;
        mutable bool _valid_values{false};
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        using Param_keys_link = Param_keys*;
        using Param_values_link = const Param_values*;

        Oper() = default;
        ~Oper() = default;
        Oper(const Oper& rhs) = default;
        Oper& operator =(const Oper& rhs) = default;
        Oper(Oper&& rhs) = default;
        Oper& operator =(Oper&& rhs) = default;
        Oper(Param_keys_link param_keys_, Param_values_link param_values_,
             const Expr& expr_);

        Param_keys& param_keys() const
            { return *_param_keys_l; }
        const Param_values& param_values() const
            { return *_param_values_l; }
        size_t size() const
            { return param_keys().size(); }
        Arg operator ()() const
            { return _f((_args_lazy.first)(), (_args_lazy.second)()); }
    protected:
        using Arg_lazy = Lazy<Arg>;
        using Args_lazy = pair<Arg_lazy, Arg_lazy>;
        using Oper_ptrs = pair<Oper_ptr, Oper_ptr>;

        Param_keys::iterator set_param_key(const Param_key& key_) const;
    private:
        Param_keys::iterator find_param_key(const Param_key& key_) const
            { return std::find(std::begin(param_keys()),
                               std::end(param_keys()), key_); }
        template <int idx>
        Arg_lazy get_arg_lazy(const Expr& expr_);
        template <int idx>
        void set_lazy_arg(const Expr& expr_)
            { get<idx>(_args_lazy) = get_arg_lazy<idx>(expr_); }
        void set_lazy_args(const Expr& expr_)
            { set_lazy_arg<0>(expr_); set_lazy_arg<1>(expr_); }
        Arg_lazy arg_lazy(Arg arg) const noexcept
            { return [arg](){ return arg; }; }
        Arg_lazy param_lazy(const Param_key& key_) const;
        Arg_lazy oper_lazy(const Oper_ptr& oper_ptr_) const;

        Param_keys_link _param_keys_l;
        Param_values_link _param_values_l;
        Bin_f _f;
        Args_lazy _args_lazy;
        Oper_ptrs _oper_ptrs;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
