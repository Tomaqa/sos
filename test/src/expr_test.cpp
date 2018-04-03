#include "test.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

namespace SOS {
    namespace Test {

        ///////////////////////////////////////////////////////////////

        using Params_expr = pair<bool, bool>;
        string expr_res(const string& input, bool should_throw, Params_expr& params)
        {
            Expr expr(input);
            Expr expr2(expr);
            if (params.first) {
                expr.simplify();
                expr2.simplify();
            }
            if (params.second) {
                expr.to_binary();
                expr2.to_binary();
            }
            if (!should_throw) {
                expect(expr == expr2,
                       "Result differ with copy of itself: "s
                       + to_string(expr) + " != " + to_string(expr2));

                cout << input << " -> " << to_string(expr) << endl;
            }
            return move(to_string(expr));
        }

        /////////////////////////////////////////////////////////////////

        bool is_flat_res(const string& input, bool, Dummy&)
        {
            return Expr(input).is_flat();
        }

        string flatten_res(const string& input, bool should_throw, Dummy&)
        {
            Expr expr(input);
            Expr expr2(expr);
            if (!should_throw) {
                expect(expr.flatten().is_flat(),
                       "'is_flat()' is false after 'flatten()': '"s + to_string(expr) + "'");
                expect(expr2.simplify().flatten().is_flat(),
                       "'is_flat()' is false after 'simplify().flatten()': '"s
                       + to_string(expr2) + "'");
                expect(expr == expr2,
                       "Flatten versions with and without 'simplify() differ: '"s
                       + to_string(expr) + "' != '"
                       + to_string(expr2) + "'");
                cout << input << " -> " << to_string(expr) << endl;
            }
            return move(to_string(expr));
        }

        /////////////////////////////////////////////////////////////////

        template <typename Arg>
        using Elems = Expr::Elems<Arg>;

        template <typename Arg>
        Elems<Arg> flat_trans_res(const string& input, bool, Dummy&)
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
            cout << expr << eval << endl;
            cout << "  =? " << res << endl;
        }

        template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
        Arg eval_res(const string& input, bool should_throw,
                     Params_eval<Arg, Param_values>& params)
        {
            Expr expr(input);
            Eval_t<Arg> eval1(expr, params._keys);
            Eval_t<Arg> eval2(eval1);
            Eval_t<Arg> eval3(expr, eval1.cparam_keys_ptr());
            Eval_t<Arg> eval4(expr, eval1.cparam_keys_ptr(),
                              eval1.param_values_ptr());
            Arg res1 = eval1(params._values);
            Arg res2 = eval2(params._values);
            Arg res3 = eval3(params._values);
            Arg res4 = eval4(params._values);
            Arg res12 = eval1(params._values);
            Arg res22 = eval2(params._values);
            Arg res32 = eval3(params._values);
            Arg res42 = eval4(params._values);
            Arg res23 = eval2(eval1.param_values_ptr());
            Arg res33 = eval3(eval1.param_values_ptr());
            Arg res43 = eval4(eval1.param_values_ptr());
            if (!should_throw) {
                expect(res1 == res2,
                       "Result differ with copy of itself: "s
                       + to_string(res1) + " != " + to_string(res2));
                expect(res1 == res3,
                       "Result differ with copy of keys pointer: "s
                       + to_string(res1) + " != " + to_string(res3));
                expect(res1 == res4,
                       "Result differ with copy of both parameter pointers: "s
                       + to_string(res1) + " != " + to_string(res4));

                expect(res1 == res12,
                       "Results of two consecutive evaluations differ: "s
                       + to_string(res1) + " != " + to_string(res12));
                expect(res2 == res22,
                       "Results of two consecutive evaluations of copy differ: "s
                       + to_string(res2) + " != " + to_string(res22));
                expect(res3 == res32,
                       "Results of two consecutive evaluations of keys pointer copy differ: "s
                       + to_string(res3) + " != " + to_string(res32));
                expect(res4 == res42,
                       "Results of two consecutive evaluations of both param. pointers copy differ: "s
                       + to_string(res4) + " != " + to_string(res42));

                expect(res1 == res23,
                       "Result differ with calling parameters by pointer at copy of itself: "s
                       + to_string(res1) + " != " + to_string(res23));
                expect(res1 == res33,
                       "Result differ with calling parameters by pointer at copy of keys pointer: "s
                       + to_string(res1) + " != " + to_string(res33));
                expect(res1 == res43,
                       "Result differ with calling parameters by pointer at copy of both param. pointers: "s
                       + to_string(res1) + " != " + to_string(res43));

                print_expr_eval_res(expr, eval1, params, res1);
            }
            return res1;
        }

        template <typename Arg, typename Param_values = typename Eval_t<Arg>::Param_values>
        Arg expr_get_eval_res(const string& input, bool should_throw,
                              Params_eval<Arg, Param_values>& params)
        {
            Expr expr(input);
            Eval_t<Arg> eval1 = expr.get_eval<Arg>(params._keys);
            Eval_t<Arg> eval2 = expr.get_eval<Arg>(params._keys);
            Arg res1 = eval1(params._values);
            Arg res2 = eval2(params._values);
            Arg res3 = Eval_t<Arg>(input, params._keys)(params._values);

            if (!should_throw) {
                expect(res1 == res2,
                       "Results of two consecutive 'Expr::get_eval's differ: "s
                       + to_string(res1) + " != " + to_string(res2));
                expect(res2 == res3,
                       "Results of 'Expr::get_eval' and direct 'Expr::eval' differ: "s
                       + to_string(res2) + " != " + to_string(res3));

                print_expr_eval_res(expr, eval1, params, res1);
            }
            return res1;
        }
    }
}

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
{
    using namespace SOS;
    using namespace SOS::Test;
    using namespace std;

    Test_data<Params_expr> expr_data = {
        {"",                                        {true, false},      "( )",                                                                     },
        {"-",                                       {true, false},      "( - )",                                                                     },
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
        {"+ 1",                                     {true, true},       "( + 0 1 )",                                                               },
        {"+ 1 2",                                   {true, true},       "( + 1 2 )",                                                               },
        {"+ 1 2 3",                                 {true, true},       "( + 1 ( + 2 3 ) )",                                                       },
        {"+ 1 2 3 4 5",                             {true, true},       "( + 1 ( + 2 ( + 3 ( + 4 5 ) ) ) )",                                       },
        {"* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",         {true, true},       "( * ( + 1 ( + 2 3 ) ) ( * ( + 4 ( + 5 6 ) ) ( + 7 ( + 8 9 ) ) ) )",       },
        {"+ 1",                                     {true, true},       "( + 0 1 )",                                                               },
        {"+ 1 2 (- 3) 4",                           {true, true},       "( + 1 ( + 2 ( + ( - 0 3 ) 4 ) ) )",                                       },
        {"+ 1 \x00 21244",                          {false, false},     "( + 1 )",                                                                 },
        {" \x00 ",                                  {false, false},     "( )",                                                                     },
    };

    Test_data<Params_expr> expr_throw_data = {
        {"(",                                      {false, false},      "",                                                                        },
        {")",                                      {false, false},      "",                                                                        },
        {"  ) ",                                   {false, false},      "",                                                                        },
        {" (  ",                                   {false, false},      "",                                                                        },
        {")(",                                     {false, false},      "",                                                                        },
        {" )  ( ",                                 {false, false},      "",                                                                        },
        {" ( ( ) ",                                {false, false},      "",                                                                        },
        {"  ( ) ) ",                               {false, false},      "",                                                                        },
        {"  x ) ",                                 {false, false},      "",                                                                        },
        {" ( x  ",                                 {false, false},      "",                                                                        },
        {" ( x ) ( ",                              {false, false},      "",                                                                        },
        {" ( ( x )  ",                             {false, false},      "",                                                                        },
        {" ( ( x ) ( ",                            {false, false},      "",                                                                        },
        {" ( ( x ) ) ) ",                          {false, false},      "",                                                                        },
        {" ( ( x ) x) ) ",                         {false, false},      "",                                                                        },
        {" ( ( x ) x) 7) ",                        {false, false},      "",                                                                        },
        {" ( ( ( x ) x) 7 ",                       {false, false},      "",                                                                        },
        {"",                                       {false, true},       "",                                                                        },
        {"1",                                      {false, true},       "",                                                                        },
        {"((1))",                                  {false, true},       "",                                                                        },
        {"x (1)",                                  {false, true},       "",                                                                        },
        {"(1) x",                                  {false, true},       "",                                                                        },
        {"+ 1 (+ 2 (+))",                          {false, true},       "",                                                                        },
        {"(+ 1 1) 1 1",                            {false, true},       "",                                                                        },
    };

    Test_data<Dummy, bool> is_flat_data = {
        {"",                                           {},                                                                   true,                 },
        {"+ 1 2",                                      {},                                                                   true,                 },
        {"+ x 2 5 1 +",                                {},                                                                   true,                 },
        {"+ x (2) 5 1 +",                              {},                                                                   false,                },
        {"+ (x 2) 5 1 +",                              {},                                                                   false,                },
    };

    Test_data<> flatten_data = {
        {"",                                                  {},                      "( )",                                                      },
        {"+ 1 2",                                             {},                      "( + 1 2 )",                                                },
        {"+ (x (2)) 5 1 +",                                   {},                      "( + x 2 5 1 + )",                                          },
        {"5  1  (-(+ abc 1) 1 2 (- 1))",                      {},                      "( 5 1 - + abc 1 1 2 - 1 )",                                },
        {"0(1(2(3)4)5)6",                                     {},                      "( 0 1 2 3 4 5 6 )",                                        },
        {"* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",                   {},                      "( * + 1 2 3 + 4 5 6 + 7 8 9 )",                            },
    };

    Test_data<Dummy, Elems<double>> flat_trans_data = {
        {"",                                                  {},                      {},                                                         },
        {"1 2",                                               {},                      {1, 2},                                                     },
        {"0 (1 2 3) (4 5 6) (7 8 9)",                         {},                      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},                             },
    };

    Test_data<Dummy, Elems<double>> flat_trans_throw_data = {
        {"1 x",                                               {},                      {},                                                         },
    };

    Test_data<Params_eval<double>, double> eval_data_double = {
        {"+ 1 2",                                      {{}, {}},                                                             1+2,                  },
        {"+ 10 x",                                     {{}, {10}},                                                           10+10,                },
        {"+ 10 (+ x x)",                               {{}, {10}},                                                           10+10+10,             },
        {"+ x y",                                      {{}, {13, 17}},                                                       13+17,                },
        {"+ x ( - 10 y)",                              {{}, {100, 50}},                                                      100+(10-50),          },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {50, 10, 20}},                                                   50+(3./10)*20-2,      },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {1, 2, 3}},                                                      1+(3./2)*3-2,         },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{}, {10, 50, 20}},                                                   10+(3./50)*20-2,      },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{"t", "x", "y"}, {10, 50, 20}},                                      50+(3./10)*20-2,      },
        {"- 0 (* y (* 5 (/ x (/ 3 2))))",              {{"x", "y"}, {60, 5}},                                                -5*5*(60./(3./2)),    },
        {"+ 1 2",                                      {{"t"}, {1}},                                                         1+2,                  },
        {"+ 1 x",                                      {{"t"}, {1, 5}},                                                      1+5,                  },
    };

    Test_data<Params_eval<double, initializer_list<double>>, double> eval_data_double_init = {
        {"+ x ( - 10 y)",                              {{}, {100, 50}, true},                                                100+(10-50),          },
        {"(+ x (- (* (/ 3 t) y) 2))",                  {{"t", "x", "y"}, {10, 50, 20}, true},                                50+(3./10)*20-2,      },
    };

    Test_data<Params_eval<double>, double> eval_throw_data_double = {
        {"+ 1 2",                                      {{}, {1}},                                                            0,                    },
        {"+ 1 2",                                      {{"x"}, {1, 2}},                                                      0,                    },
        {"+ 1 x",                                      {{"x"}, {1, 2}},                                                      0,                    },
        {"+ 1 x",                                      {{"y"}, {1, 2, 3}},                                                   0,                    },
        {"+ 1",                                        {{}, {}},                                                             0,                    },
        {"+",                                          {{}, {}},                                                             0,                    },
        {"1",                                          {{}, {}},                                                             0,                    },
        {"+ 1 1 1",                                    {{}, {}},                                                             0,                    },
        {"(+) 1 1",                                    {{}, {}},                                                             0,                    },
        {"(+ 1 1) 1 1",                                {{}, {}},                                                             0,                    },
        {"1 1 1",                                      {{}, {}},                                                             0,                    },
        {"# 1 1",                                      {{}, {}},                                                             0,                    },
        {"+ 1 (# 1 1)",                                {{}, {}},                                                             0,                    },
    };

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

    string expr_msg = "building of expressions";
    test<Params_expr, string, string>(expr_data, expr_res, expr_msg);
    test<Params_expr, string, string>(expr_throw_data, expr_res, expr_msg, true);

    test<Dummy, bool, string>(is_flat_data, is_flat_res, "checking of flat state");
    test<Dummy, string, string>(flatten_data, flatten_res, "flattening the expressions");

    string flat_trans_msg = "transforming expressions to arrays of values";
    test<Dummy, Elems<double>, string>(flat_trans_data, flat_trans_res<double>, flat_trans_msg);
    test<Dummy, Elems<double>, string>(flat_trans_throw_data, flat_trans_res<double>, flat_trans_msg, true);

    string eval_msg = "evaluation of expressions via evaluation objects";
    test<Params_eval<double>,
         double, string>
         (eval_data_double, eval_res<double>, eval_msg);
    test<Params_eval<double, initializer_list<double>>,
         double, string>
         (eval_data_double_init, eval_res<double, initializer_list<double>>, eval_msg);
    test<Params_eval<double>,
         double, string>
         (eval_throw_data_double, eval_res<double>, eval_msg, true);

    string expr_get_eval_msg = "evaluation of expressions from within expression objects";
    test<Params_eval<double>,
         double, string>
         (eval_data_double, expr_get_eval_res<double>, expr_get_eval_msg);
    test<Params_eval<double, initializer_list<double>>,
         double, string>
         (eval_data_double_init, expr_get_eval_res<double, initializer_list<double>>, expr_get_eval_msg);

    cout << endl << "Success." << endl;
    return 0;
}
