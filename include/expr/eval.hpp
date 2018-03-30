#ifndef ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
#define ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430

#include "expr.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Param_key = Token;
        using Param_keys = vector<Param_key>;
        using Param_values = vector<Arg>;

        Eval() = default;
        ~Eval() = default;
        Eval(const Eval& eval) = delete;
        Eval& operator =(const Eval& eval) = delete;
        Eval(Eval&& eval) = default;
        Eval& operator =(Eval&& eval) = default;
        Eval(const Expr& expr, Param_keys param_keys = {})
            : _params{move(param_keys), {}}, _oper(&_params, expr) { }
        Eval(const string& str, Param_keys param_keys = {})
            : Eval(Expr(str), move(param_keys)) { }

        size_t size() const
            { return coper().size(); }
        const Param_keys& cparam_keys() const
            { return coper().cparam_keys(); }
        const Param_values& cparam_values() const
            { return coper().cparam_values(); }

        Arg operator () (initializer_list<Arg> list)
            { return call(move(list)); }
        Arg operator () (Param_values param_values)
            { return call(move(param_values)); }
    protected:
        class Oper;
        using Param = pair<Param_key, Arg>;
        using Params = pair<Param_keys, Param_values>;
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
            { return oper().param_keys(); }
        Param_values& param_values()
            { return oper().param_values(); }
        const Oper& coper() const { return _oper; }
        Oper& oper() { return _oper; }

        static Oper_ptr new_oper(Oper&& oper_)
            { return make_unique<Oper>(move(oper_)); }
        static Oper* oper_link(const Oper_ptr& oper_ptr)
            { return oper_ptr.get(); }
    private:
        template <typename Cont>
        Arg call(Cont&& cont);

        Params _params;
        Oper _oper;
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        using Params_link = Params*;

        Oper() : _params_l(nullptr), _oper_ptrs{nullptr, nullptr} { }
        ~Oper() = default;
        Oper(const Oper& oper) = delete;
        Oper& operator =(const Oper& oper) = delete;
        Oper(Oper&& oper) = default;
        Oper& operator =(Oper&& oper) = default;
        Oper(Params_link params, const Expr& expr);

        const Param_keys& cparam_keys() const
            { return cparams().first; }
        const Param_values& cparam_values() const
            { return cparams().second; }
        Param_keys& param_keys()
            { return params().first; }
        Param_values& param_values()
            { return params().second; }
        size_t size() const
            { return cparam_keys().size(); }
        Arg operator () () const
            { return _f((_arg_fs.first)(), (_arg_fs.second)()); }
    protected:
        using Arg_f = function<Arg()>;
        using Arg_fs = pair<Arg_f, Arg_f>;
        using Oper_ptrs = pair<Oper_ptr, Oper_ptr>;

        const Params& cparams() const { return *_params_l; }
        Params& params() { return *_params_l; }
        Param_keys::iterator set_param_key(const Param_key& key);
    private:
        Param_keys::iterator find_param_key(const Param_key& key)
            { return std::find(std::begin(param_keys()),
                               std::end(param_keys()), key); }
        template <size_t idx>
        Arg_f get_arg_f(const Expr& expr);
        template <size_t idx>
        void set_arg_f(const Expr& expr)
            { get<idx>(_arg_fs) = get_arg_f<idx>(expr); }
        void set_arg_fs(const Expr& expr)
            { set_arg_f<0>(expr); set_arg_f<1>(expr); }
        Arg_f arg_f(Arg arg)
            { return [arg](){ return arg; }; }
        Arg_f param_f(const Param_key& key);
        Arg_f oper_f(const Oper_ptr& oper_ptr);

        Params_link _params_l;
        Bin_f _f;
        Arg_fs _arg_fs;
        Oper_ptrs _oper_ptrs;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
