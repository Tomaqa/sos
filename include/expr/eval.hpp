#ifndef ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
#define ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430

#include "expr.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Bin_f = function<Arg(Arg, Arg)>;
        using F_key = const string;
        template <typename F>
        using F_pair = pair<F_key, F>;
        template <typename F>
        using F_map = Const_map<typename F_pair<F>::first_type,
                                typename F_pair<F>::second_type>;
        static const F_map<Bin_f> bin_fs;

        using Param_key = Token_t;
        using Param_keys = vector<Param_key>;
        using Param_values = vector<Arg>;

        class Oper;

        Eval() = default;
        ~Eval() = default;
        Eval(const Eval& eval) = delete;
        Eval& operator =(const Eval& eval) = delete;
        Eval(Eval&& eval) = default;
        Eval& operator =(Eval&& eval) = default;
        Eval(const Exprs& exprs)
            // : _oper(&_params, exprs) { }
            // : _oper(_params, exprs) { }
            : _oper_ptr(new_oper(Oper(_params, exprs))) { }
        // Eval(Exprs& exprs, bool is_binary = true)
            // : Eval(cref(is_binary ? exprs : exprs.to_binary())) { }
        Eval(const string& str)
            : Eval(Exprs(str)) { }

        size_t size() const
            { return oper().size(); }
        Param_keys& param_keys()
            { return oper().param_keys(); }
        const Param_keys& param_keys() const
            { return oper().param_keys(); }
        Param_values& param_values()
            { return oper().param_values(); }
        const Param_values& param_values() const
            { return oper().param_values(); }

        Arg operator () (initializer_list<Arg> list);
    protected:
        using Param = pair<Param_key, Arg>;
        using Params = pair<Param_keys, Param_values>;
        using Oper_ptr = unique_ptr<Oper>;

        // const Oper& oper() const { return _oper; }
        // Oper& oper() { return _oper; }
        const Oper& oper() const { return *_oper_ptr; }
        Oper& oper() { return *_oper_ptr; }
        static Oper_ptr new_oper(Oper&& oper_)
            { return make_unique<Oper>(move(oper_)); }
    private:
        Params _params;
        // Oper _oper;
        Oper_ptr _oper_ptr;
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        using Params_link = Params&;

        Oper() = delete;
        ~Oper() = default;
        Oper(const Oper& oper) = delete;
        Oper& operator =(const Oper& oper) = delete;
        Oper(Oper&& oper) = default;
        Oper& operator =(Oper&& oper) = default;
        Oper(Params_link params, const Exprs& exprs);

        Param_keys& param_keys()
            { return params().first; }
        const Param_keys& param_keys() const
            { return params().first; }
        Param_values& param_values()
            { return params().second; }
        const Param_values& param_values() const
            { return params().second; }
        size_t size() const
            { return param_keys().size(); }
        Arg operator () () const
            { return _f((_arg_fs.first)(), (_arg_fs.second)()); }
    protected:
        using Arg_f = function<Arg()>;
        using Arg_fs = pair<Arg_f, Arg_f>;
        using Oper_ptrs = pair<Oper_ptr, Oper_ptr>;

        const Params& params() const { return _params_l; }
        Params& params() { return _params_l; }
        Param_keys::iterator set_param_key(const Param_key& key);
    private:
        Param_keys::iterator find_param_key(const Param_key& key)
            { return find(begin(param_keys()), end(param_keys()), key); }
        template <size_t idx>
        Arg_f get_arg_f(const Exprs& exprs);
        template <size_t idx>
        void set_arg_f(const Exprs& exprs)
            { get<idx>(_arg_fs) = get_arg_f<idx>(exprs); }
        void set_arg_fs(const Exprs& exprs)
            { set_arg_f<0>(exprs); set_arg_f<1>(exprs); }
        Arg_f arg_f(Arg arg)
            { return [arg](){ return arg; }; }
        Arg_f param_f(const Param_values& params, const size_t idx)
            { return [&params, idx](){ return params[idx]; }; }
        // Arg_f oper_f(const Oper& oper)
        //     { return [&](){ cout << "OPER?" << endl << &oper << endl; return oper(); }; }
        Arg_f oper_f(const Oper *const oper_ptr)
            { return [oper_ptr](){ return (*oper_ptr)(); }; }

        Params_link _params_l;
        Bin_f _f;
        Arg_fs _arg_fs;
        Oper_ptrs _oper_ptrs;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
