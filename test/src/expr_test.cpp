#include "test.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

using namespace Test;

///////////////////////////////////////////////////////////////

using Params_expr = pair<bool, bool>;
string expr_res(const string& input, Params_expr& params)
{
    Expr expr(input);
    if (params.first) expr.simplify();
    if (params.second) expr.to_binary();
    cout << input << " -> " << (string)expr << endl;
    return move((string)expr);
}

/////////////////////////////////////////////////////////////////

bool is_flat_res(const string& input, Dummy&)
{
    return Expr(input).is_flat();
}

string flatten_res(const string& input, Dummy&)
{
    Expr expr(input);
    Expr expr2(expr);
    expect(expr.flatten().is_flat(),
           "'is_flat()' is false after 'flatten()': '"s + (string)expr + "'");
    expect(expr2.simplify().flatten().is_flat(),
           "'is_flat()' is false after 'simplify().flatten()': '"s
           + (string)expr2 + "'");
    expect(expr == expr2,
           "Flatten versions with and without 'simplify() differ: '"s
           + (string)expr + "' != '"
           + (string)expr2 + "'");
    cout << input << " -> " << (string)expr << endl;
    return move((string)expr);
}

/////////////////////////////////////////////////////////////////

template <typename Arg>
using Elems = Expr::Elems<Arg>;

template <typename Arg>
Elems<Arg> flat_trans_res(const string& input, Dummy&)
{
    return Expr(input).flatten().flat_transform<Arg>();
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

    expect(res1 == res2,
           "Results of two consecutive 'Expr::get_eval's differ: "s
           + to_string(res1) + " != " + to_string(res2));
    expect(res2 == res3,
           "Results of 'Expr::get_eval' and direct 'Expr::eval' differ: "s
           + to_string(res2) + " != " + to_string(res3));

    print_expr_eval_res(expr, eval1, params, res1);
    return res1;
}

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
{
    TestData<Params_expr> expr_data = {
        {"",                                        {true, false},      "( )",                                                                     },
        {"  ",                                      {true, false},      "( )",                                                                     },
        {" 1 ",                                     {true, false},      "( 1 )",                                                                   },
        {"1 2 3",                                   {true, false},      "( 1 2 3 )",                                                               },
        {"5  1  (-(+ abc 1) 1 2 (- 1))",            {true, false},      "( 5 1 ( - ( + abc 1 ) 1 2 ( - 1 ) ) )",                                   },
        {"()",                                      {true, false},      "( )",                                                                     },
        {"()",                                      {false, false},     "( )",                                                                     },
        {"(())",                                    {true, false},      "( )",                                                                     },
        {"(())",                                    {false, false},     "( ( ) )",                                                                 },
        {"((()))",                                  {true, false},      "( )",                                                                     },
        {"((()))",                                  {false, false},     "( ( ( ) ) )",                                                             },
        {"0(1(2(3)4)5)6",                           {true, false},      "( 0 ( 1 ( 2 3 4 ) 5 ) 6 )",                                               },
        {"0(1(2(3)4)5)6",                           {false, false},      "( 0 ( 1 ( 2 ( 3 ) 4 ) 5 ) 6 )",                                          },
        {"1 (+ 2 (3))",                             {true, false},      "( 1 ( + 2 3 ) )",                                                         },
        {"(1) (+ 2 (3))",                           {true, false},      "( 1 ( + 2 3 ) )",                                                         },
        {"(1) (+ 2 (3))",                           {false, false},     "( ( 1 ) ( + 2 ( 3 ) ) )",                                                 },
        {" (1 2 3)",                                {true, false},      "( 1 2 3 )",                                                               },
        {" (1 2 3)",                                {false, false},     "( 1 2 3 )",                                                               },
        {" ((1) 2) ( ( 3) )",                       {true, false},      "( ( 1 2 ) 3 )",                                                           },
        {" ((1) 2) ( ( 3) )",                       {false, false},     "( ( ( 1 ) 2 ) ( ( 3 ) ) )",                                               },
        {"+ 1 2",                                   {true, true},       "( + 1 2 )",                                                               },
        {"+ 1 2 3",                                 {true, true},       "( + 1 ( + 2 3 ) )",                                                       },
        {"+ 1 2 3 4 5",                             {true, true},       "( + 1 ( + 2 ( + 3 ( + 4 5 ) ) ) )",                                       },
        {"* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",         {true, true},       "( * ( + 1 ( + 2 3 ) ) ( * ( + 4 ( + 5 6 ) ) ( + 7 ( + 8 9 ) ) ) )",       },
        {"+ 1",                                     {true, true},       "( + 0 1 )",                                                               },
        {"+ 1 2 (- 3) 4",                           {true, true},       "( + 1 ( + 2 ( + ( - 0 3 ) 4 ) ) )",                                       },
    };

    TestData<Dummy, bool> is_flat_data = {
        {"",                                           {},                                                                   true,                 },
        {"+ 1 2",                                      {},                                                                   true,                 },
        {"+ x 2 5 1 +",                                {},                                                                   true,                 },
        {"+ x (2) 5 1 +",                              {},                                                                   false,                },
        {"+ (x 2) 5 1 +",                              {},                                                                   false,                },
    };

    TestData<> flatten_data = {
        {"",                                                  {},                      "( )",                                                      },
        {"+ 1 2",                                             {},                      "( + 1 2 )",                                                },
        {"+ (x (2)) 5 1 +",                                   {},                      "( + x 2 5 1 + )",                                          },
        {"5  1  (-(+ abc 1) 1 2 (- 1))",                      {},                      "( 5 1 - + abc 1 1 2 - 1 )",                                },
        {"0(1(2(3)4)5)6",                                     {},                      "( 0 1 2 3 4 5 6 )",                                        },
        {"* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",                   {},                      "( * + 1 2 3 + 4 5 6 + 7 8 9 )",                            },
    };

    TestData<Dummy, Elems<double>> flat_trans_data = {
        {"",                                                  {},                      {},                                                         },
        {"1 2",                                               {},                      {1, 2},                                                     },
        {"1 x",                                               {},                      {1, 0},                                                     },
        {"0 (1 2 3) (4 5 6) (7 8 9)",                         {},                      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},                             },
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
        {"+ 1 2",                                      {{"t"}, {1}},                                                         1+2,                  },
        {"+ 1 x",                                      {{"t"}, {1, 5}},                                                      1+5,                  },
    };

    TestData<Params_eval<double, initializer_list<double>>, double> eval_data_double_init = {
        {"+ x ( - 10 y)",                              {{}, {100, 50}, true},                                                100+(10-50),          },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{"t", "x", "y"}, {10, 50, 20}, true},                                50+(3./10)*20-2,      },
    };

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

    test<Params_expr, string, string>(expr_data, expr_res, "building of expressions");

    test<Dummy, bool, string>(is_flat_data, is_flat_res, "checking of flat state");
    test<Dummy, string, string>(flatten_data, flatten_res, "flattening the expressions");

    test<Dummy, Elems<double>, string>(flat_trans_data, flat_trans_res<double>, "transforming expressions to arrays of values");

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

    // ! netestuju FAIL pripady, kdy to ma hodit vyjimku

    cout << endl << "Success." << endl;
    return 0;
}
