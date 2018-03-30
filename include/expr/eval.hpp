#ifndef ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
#define ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430

#include "expr.hpp"

namespace SOS {
    template <typename Arg>
    class Expr::Eval {
    public:
        using Bin_f = function<Arg(Arg, Arg)>;
        using F_key = const char*;
        template <typename F>
        using F_map = Const_map<F_key, F>;
        static const F_map<Bin_f> bin_fs;

        class Oper;

        ~Eval() = default;
        Eval(const Exprs& exprs);
        Eval(Exprs& exprs, bool is_binary = true)
            : Eval(cref(is_binary ? exprs : exprs.to_binary())) { }
        Eval(const string& str)
            : Eval(Exprs(str)) { }
    protected:
        using Param_key = Token_t;
        using Params = map<Param_key, Arg>;
    private:
        Params _params;
        Oper _oper;
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        ~Oper() = default;
        Oper(Params& params, const Exprs& exprs);
        // operator Arg() const { return _f(); }
    protected:
        // using Args = pair<Arg&, Arg&>;
        using Args = pair<Arg, Arg>;
        // using Arg_ref = const Arg&;
        // using Arg_refs = pair<Arg_ref, Arg_ref>;
        // using Arg_ptr = Arg*;
        // using Arg_ptrs = pair<Arg_ptr, Arg_ptr>;
        // using Arg_f = Arg*;
        using Arg_f = function<Arg()>;
        using Arg_fs = pair<Arg_f, Arg_f>;

        bool add_param(Param_key key);
        Arg_f param_ptr(Param_key key) const;
    private:
        // void set_arg(const Exprs& exprs, size_t idx);
        // void set_arg_ptr(const Exprs& exprs, size_t idx);
        // Arg_ptr get_arg_ptr(const Exprs& exprs, size_t idx);
        Arg_f get_arg_f(const Exprs& exprs, size_t idx);

        Bin_f _f;
        Args _args;
        // Arg_refs _arg_refs;
        // Arg_ptrs _arg_ptrs;
        Arg_fs _arg_fs;
        Params& _params;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
