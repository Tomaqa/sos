#include "sos.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

using namespace SOS;

template <typename Params, typename Output = string, typename Input = string>
using TestCase = tuple<const Input, Params, const Output>;
template <typename Params, typename Output = string, typename Input = string>
using TestData = vector<TestCase<Params, Output, Input>>;

template <typename Output = string>
void test_case(const Output& expect, const Output& res)
{
    if (res == expect) return;
    ostringstream oss1, oss2;
    oss1 << expect;
    oss2 << res;
    throw Error("!! Mismatch: expected: '"s + oss1.str()
                + "', got: '" + oss2.str() + "' !!");
}

template <typename Params, typename Output = string, typename Input = string>
void test(TestData<Params, Output, Input>& tdata,
          function<Output(const Input&, Params&)> f,
          const string& msg = "")
{
    if (!msg.empty()) {
        cout << "  " << string(msg.size()+16, '-') << "  " << endl;
        cout << "// Testing " << msg << " ...   \\\\" << endl;
    }
    for (auto& t : tdata) {
        const Input& input = get<0>(t);
        Params& params = get<1>(t);
        const Output& expect = get<2>(t);
        const Output& res = f(input, params);
        test_case(expect, res);
    }
    if (!msg.empty()) {
        cout << "\\\\ Testing " << msg << " done. //" << endl;
        cout << "  " << string(msg.size()+16, '-') << "  " << endl;
        cout << endl;
    }
}

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

using Params_expr = bool;
string expr_res(const string& input, Params_expr& to_binary)
{
    Expr expr(input);
    if (to_binary) expr.to_binary();
    return move((string)expr);
}

/////////////////////////////////////////////////////////////////

template <typename Arg>
using Eval_t = Expr::Eval<Arg>;
template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
struct Params_eval {
    typename Eval_t<Arg>::Param_keys _keys;
    Param_values _values;
    bool _quiet{false};
};

template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
void print_expr_eval_res(const Expr& expr, const Eval_t<Arg>& eval,
                         Params_eval<Arg, Param_values>& params, Arg res)
{
    if (params._quiet) return;
    params._quiet = true;
    cout << expr;
    cout << "[ ";
    for (const auto& k : eval.cparam_keys()) {
        cout << k << " ";
    }
    cout << "] <-- [ ";
    for (const auto& v : eval.cparam_values()) {
        cout << v << " ";
    }
    cout << "]" << endl;
    cout << "  =? " << res << endl;
}

template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
Arg eval_res(const string& input, Params_eval<Arg, Param_values>& params)
{
    Expr expr(input);
    Eval_t<Arg> eval(expr.to_binary(), params._keys);
    Arg res = eval(params._values);
    print_expr_eval_res(expr, eval, params, res);
    return res;
}

template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
Arg expr_get_eval_res(const string& input, Params_eval<Arg, Param_values>& params)
{
    Expr expr(input);
    Eval_t<Arg> eval1 = expr.get_eval<Arg>(params._keys);
    Eval_t<Arg> eval2 = expr.get_eval<Arg>(params._keys);
    Arg res1 = eval1(params._values);
    Arg res2 = eval2(params._values);
    Arg res3 = Expr(input).eval<Arg>(params._values, params._keys);

    if (res1 != res2) {
        throw Error("Results of two consecutive 'Expr::get_eval's differ: "s
                    + to_string(res1) + " != " + to_string(res2));
    }
    if (res2 != res3) {
        throw Error("Results of 'Expr::get_eval' and direct 'Expr::eval' differ: "s
                    + to_string(res2) + " != " + to_string(res3));
    }

    print_expr_eval_res(expr, eval1, params, res1);
    return res1;
}

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
{
    TestData<Params_expr> expr_data = {
        {"",                                        false,      "( )",                                                                             },
        {"  ",                                      false,      "( )",                                                                             },
        {" 1 ",                                     false,      "( 1 )",                                                                           },
        {"1 2 3",                                   false,      "( 1 2 3 )",                                                                       },
        {"5  1  (-(+ abc 1) 1 2 (- 1))",            false,      "( 5 1 ( - ( + abc 1 ) 1 2 ( - 1 ) ) )",                                           },
        {"((()))",                                  false,      "( )",                                                                             },
        {"0(1(2(3)4)5)6",                           false,      "( 0 ( 1 ( 2 3 4 ) 5 ) 6 )",                                                       },
        {"1 (+ 2 (3))",                             false,      "( 1 ( + 2 3 ) )",                                                                 },
        {"(1) (+ 2 (3))",                           false,      "( 1 ( + 2 3 ) )",                                                                 },
        {" (1 2 3)",                                false,      "( 1 2 3 )",                                                                       },
        {" ((1) 2) ( ( 3) )",                       false,      "( ( 1 2 ) 3 )",                                                                   },
        {"+ 1 2",                                   true,       "( + 1 2 )",                                                                       },
        {"+ 1 2 3",                                 true,       "( + 1 ( + 2 3 ) )",                                                               },
        {"+ 1 2 3 4 5",                             true,       "( + 1 ( + 2 ( + 3 ( + 4 5 ) ) ) )",                                               },
        {"* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",         true,       "( * ( + 1 ( + 2 3 ) ) ( * ( + 4 ( + 5 6 ) ) ( + 7 ( + 8 9 ) ) ) )",               },
        {"+ 1",                                     true,       "( + 0 1 )",                                                                       },
        {"+ 1 2 (- 3) 4",                           true,       "( + 1 ( + 2 ( + ( - 0 3 ) 4 ) ) )",                                               },
    };

    TestData<Params_eval<double>, double> eval_data_double = {
        {"+ 1 2",                                      {{}, {}},                                                             1+2,                  },
        {"+ 10 x",                                     {{}, {10}},                                                           10+10,                },
        {"+ x y",                                      {{}, {13, 17}},                                                       13+17,                },
        {"+ x ( - 10 y)",                              {{}, {100, 50}},                                                      100+(10-50),          },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {50, 10, 20}},                                                   50+(3./10)*20-2,      },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {1, 2, 3}},                                                      1+(3./2)*3-2,         },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {10, 50, 20}},                                                   10+(3./50)*20-2,      },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{"t", "x", "y"}, {10, 50, 20}},                                      50+(3./10)*20-2,      },
        {"- (* y 5 (/ x 3 2))",                        {{"x", "y"}, {60, 5}},                                                -5*5*(60./(3./2)),    },
    };

    TestData<Params_eval<double, initializer_list<double>>, double> eval_data_double_init = {
        {"+ x ( - 10 y)",                              {{}, {100, 50}, true},                                                100+(10-50),          },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{"t", "x", "y"}, {10, 50, 20}, true},                                50+(3./10)*20-2,      },
    };

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

    try {
        test<Params_expr, string, string>(expr_data, expr_res, "building of expressions");

        string eval_msg = "evaluation of expressions via evaluation objects";
        test<Params_eval<double>,
             double, string>
             (eval_data_double, eval_res<double>, eval_msg);
        test<Params_eval<double, initializer_list<double>>,
             double, string>
             (eval_data_double_init, eval_res<double, initializer_list<double>>, eval_msg);

        string expr_get_eval_msg = "evaluation of expressions from within expression objects";
        test<Params_eval<double>,
             double, string>
             (eval_data_double, expr_get_eval_res<double>, expr_get_eval_msg);
        test<Params_eval<double, initializer_list<double>>,
             double, string>
             (eval_data_double_init, expr_get_eval_res<double, initializer_list<double>>, expr_get_eval_msg);

    }
    catch (const Error& e) {
        cerr << e << endl;
        throw;
    }

    cout << endl << "Success." << endl;

    return 0;
}
