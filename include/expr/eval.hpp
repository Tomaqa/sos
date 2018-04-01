#ifndef ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
#define ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430

#include "expr.hpp"

#include <functional>

using std::function;
using std::bind;

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Param_key = Token;
        using Param_keys = vector<Param_key>;
        using Param_values = vector<Arg>;

        Eval() = default;
        ~Eval() = default;
        Eval(const Eval& rhs) = delete;
        Eval& operator =(const Eval& rhs) = delete;
        Eval(Eval&& rhs) = default;
        Eval& operator =(Eval&& rhs) = default;
        Eval(const Expr& expr_, Param_keys param_keys_ = {})
            : _param_keys{move(param_keys_)},
              _oper(&_param_keys, &_param_values, expr_) { }
        Eval(const string& str, Param_keys param_keys_ = {})
            : Eval(Expr(str), move(param_keys_)) { }

        size_t size() const
            { return cparam_keys().size(); }
        const Param_keys& cparam_keys() const
            { return _param_keys; }
        const Param_values& cparam_values() const
            { return _param_values; }

        Arg operator ()(initializer_list<Arg> list) const
            { return call(move(list)); }
        Arg operator ()(Param_values param_values_) const
            { return call(move(param_values_)); }
    protected:
        class Oper;
        using Oper_ptr = unique_ptr<Oper>;

        using Bin_f = function<Arg(Arg, Arg)>;
        using F_key = const string;
        template <typename F>
        using F_pair = pair<F_key, F>;
        template <typename F>
        using F_map = Const_map<typename F_pair<F>::first_type,
                                typename F_pair<F>::second_type>;
        static const F_map<Bin_f> bin_fs;

        Param_keys& param_keys()
            { return _param_keys; }
        Param_values& param_values() const
            { return _param_values; }
        const Oper& coper() const { return _oper; }
        Oper& oper() { return _oper; }

        static Oper_ptr new_oper(Oper&& oper_)
            { return make_unique<Oper>(move(oper_)); }
        static Oper* oper_link(const Oper_ptr& oper_ptr_)
            { return oper_ptr_.get(); }
    private:
        template <typename Cont>
        Arg call(Cont&& cont) const;

        Param_keys _param_keys;
        mutable Param_values _param_values;
        Oper _oper;
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        using Param_keys_link = Param_keys*;
        using Param_values_link = const Param_values*;

        Oper() : _param_keys_l(nullptr), _param_values_l(nullptr),
                 _oper_ptrs{nullptr, nullptr} { }
        ~Oper() = default;
        Oper(const Oper& rhs) = delete;
        Oper& operator =(const Oper& rhs) = delete;
        Oper(Oper&& rhs) = default;
        Oper& operator =(Oper&& rhs) = default;
        Oper(Param_keys_link param_keys_, Param_values_link param_values_,
             const Expr& expr_);

        Param_keys& param_keys() const
            { return *_param_keys_l; }
        const Param_values& param_values() const
            { return *_param_values_l; }
        size_t size() const
            { return cparam_keys().size(); }
        Arg operator ()() const
            { return _f((_arg_fs.first)(), (_arg_fs.second)()); }
    protected:
        using Arg_f = function<Arg()>;
        using Arg_fs = pair<Arg_f, Arg_f>;
        using Oper_ptrs = pair<Oper_ptr, Oper_ptr>;

        Param_keys::iterator set_param_key(const Param_key& key_) const;
    private:
        Param_keys::iterator find_param_key(const Param_key& key_) const
            { return std::find(std::begin(param_keys()),
                               std::end(param_keys()), key_); }
        template <int idx>
        Arg_f get_arg_f(const Expr& expr_);
        template <int idx>
        void set_arg_f(const Expr& expr_)
            { get<idx>(_arg_fs) = get_arg_f<idx>(expr_); }
        void set_arg_fs(const Expr& expr_)
            { set_arg_f<0>(expr_); set_arg_f<1>(expr_); }
        Arg_f arg_f(Arg arg) const noexcept
            { return [arg](){ return arg; }; }
        Arg_f param_f(const Param_key& key_) const;
        Arg_f oper_f(const Oper_ptr& oper_ptr_) const;

        Param_keys_link _param_keys_l;
        Param_values_link _param_values_l;
        Bin_f _f;
        Arg_fs _arg_fs;
        Oper_ptrs _oper_ptrs;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
