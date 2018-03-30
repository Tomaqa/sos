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
        Eval(const Exprs& exprs)
            // : _oper(_params, exprs) { }
            // : _oper(&_params, exprs) { }
            : _oper(this, exprs) { }
        Eval(Exprs& exprs, bool is_binary = true)
            : Eval(cref(is_binary ? exprs : exprs.to_binary())) { }
        Eval(const string& str)
            : Eval(Exprs(str)) { }

        size_t size() const
            { return _oper.size(); }
        Param_keys param_keys() const;
        Arg operator () (initializer_list<Arg> list);
    protected:
        using Param = pair<Param_key, Arg>;
        // using Params = map<typename Param::first_type,
        // using Params = map<typename Param::first_type,
                           // typename Param::second_type>;
        // using Params = vector<Param>;
        using Params = pair<Param_keys, Param_values>;

        // bool set_param_value(const Param_key& key, Arg value);
        // bool set_param_value(const Param& param)
        //     { return set_param_value(param.first, param.second); }
    private:
        Params _params;
        // Param_keys _param_keys;
        // Param_values _param_values;
        Oper _oper;
    };

    template <typename Arg>
    class Expr::Eval<Arg>::Oper {
    public:
        // using Params_ptr = Params*;
        using Params_ptr = Expr::Eval<Arg>*;

        Oper() : _params_ptr(nullptr) { }
        ~Oper() = default;
        // Oper(Params& params, const Exprs& exprs);
        Oper(Params_ptr params_ptr, const Exprs& exprs);

        Param_keys& param_keys()
            // { return _params_ptr->first; }
            { return _params_ptr->_params.first; }
        const Param_keys& param_keys() const
            // { return _params_ptr->first; }
            { return _params_ptr->_params.first; }
        Param_values& param_values()
            // { return _params_ptr->second; }
            { return _params_ptr->_params.second; }
        const Param_values& param_values() const
            // { return _params_ptr->second; }
            { return _params_ptr->_params.second; }
        size_t size() const
            // { return _params.first.size(); }
            // { return _params_ptr->first.size(); }
            { return param_keys().size(); }
        Arg operator () () const { return _f(_arg_fs.first(), _arg_fs.second()); }
    protected:
        using Arg_f = function<Arg()>;
        using Arg_fs = pair<Arg_f, Arg_f>;

        Param_keys::iterator find_param_key(const Param_key& key)
            // { return find(begin(_params.first), end(_params.first), key); }
        // auto find_param_key(const Param_key& key)
            // { return find(begin(_params_ptr->first), end(_params_ptr->first), key); }
            // { return move(find(begin(_params_ptr->first), end(_params_ptr->first), key)); }
            { return find(begin(param_keys()), end(param_keys()), key); }
            // { return begin(param_keys()); }
        // Param_keys::const_iterator c_find_param_key(const Param_key& key) const
            // { return find(cbegin(_params.first), cend(_params.first), key); }
            // { return find(cbegin(_params_ptr->first), cend(_params_ptr->first), key); }
            // { return find(_params_ptr->first.cbegin(), _params_ptr->first.cend(), key); }
        void set_param_key(const Param_key& key);
            // { _params[key]; }
            // { find(begin(_params.first), end(_params.first, key)) _params[key]; }
        // const Arg& param_value(const Param_key& key) const;
        const Arg& param_value(const Param_key& key);
            // { return _params.at(key); }
        // Arg_f param_f(const Param_key& key) const
        Arg_f param_f(const Param_key& key)
            // { cout << "@!$! " << key << endl; return [&](){ return param_value(key); }; }
            { cout << "@!$! " << key << endl; return [this, key](){ return param_value(key); }; }
    private:
        // Arg_f get_arg_f(const Exprs& exprs, size_t idx);
        Arg_f get_arg_f(const Expr_ptr& expr);

        Bin_f _f;
        Arg_fs _arg_fs;
        // Params& _params;
        Params_ptr _params_ptr;
        // Param_keys& _param_keys;
        // const Param_values& _param_values;
    };
}

#include "expr/eval.tpp"

#endif // ___SOS_EVAL_H_OUDH983489G84G5093G04GJ40H45T938HJ3409FG430
