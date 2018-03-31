#include "sos.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

using namespace SOS;

void test(const string& res, const string& expect)
{
    if (res == expect) return;
    throw Error("Mismatch: expected: '"s + expect + "', got: '" + res + "'");
}

void flat_extract_braces_test(istringstream&& iss, const string& expect)
{
    test(Expr_place::flat_extract_braces(move(iss)).str(), expect);
}

void test_expr(const string& str, const string& expect, bool to_binary = false)
{
    Expr expr(str);
    if (to_binary) expr.to_binary();
    test((string)expr, expect);
}

int main(int, const char*[])
{
    try {
      flat_extract_braces_test(istringstream("()"), "");
      flat_extract_braces_test(istringstream("  ()  "), "");
      flat_extract_braces_test(istringstream("  (  )  "), "  ");
      flat_extract_braces_test(istringstream("  ( 1  )  "), " 1  ");
      flat_extract_braces_test(istringstream("  (1  )  "), "1  ");
      flat_extract_braces_test(istringstream("  (1)  "), "1");
      flat_extract_braces_test(istringstream("  ( 1)  "), " 1");

      test_expr("",        "( )");
      test_expr("  ",      "( )");
      test_expr(" 1 ",     "( 1 )");
      test_expr("1 2 3",    "( 1 2 3 )");
      test_expr("5  1  (-(+ abc 1) 1 2 (- 1))", "( 5 1 ( - ( + abc 1 ) 1 2 ( - 1 ) ) )");
      test_expr("((()))", "( )");
      test_expr("0(1(2(3)4)5)6", "( 0 ( 1 ( 2 3 4 ) 5 ) 6 )");
      test_expr("1 (+ 2 (3))",    "( 1 ( + 2 3 ) )");
      test_expr("(1) (+ 2 (3))",  "( 1 ( + 2 3 ) )");
      test_expr(" (1 2 3)", "( 1 2 3 )");
      test_expr(" ((1) 2) ( ( 3) )", "( ( 1 2 ) 3 )");
      test_expr("+ 1 2",    "( + 1 2 )", true);
      test_expr("+ 1 2 3",    "( + 1 ( + 2 3 ) )", true);
      test_expr("+ 1 2 3 4 5",    "( + 1 ( + 2 ( + 3 ( + 4 5 ) ) ) )", true);
      test_expr("* (+ 1 2 3) (+ 4 5 6) (+ 7 8 9)",    "( * ( + 1 ( + 2 3 ) ) ( * ( + 4 ( + 5 6 ) ) ( + 7 ( + 8 9 ) ) ) )", true);
      test_expr("+ 1",    "( + 0 1 )", true);
      test_expr("+ 1 2 (- 3) 4",    "( + 1 ( + 2 ( + ( - 0 3 ) 4 ) ) )", true);

      using Eval_t = Expr::Eval<double>;
      Eval_t e1;
      e1 = Eval_t(Expr("+ 1 2"));
      for (auto& k : e1.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e1({}) << endl << endl;

      Eval_t e2("+ 10 x");
      for (auto& k : e2.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e2({10}) << endl << endl;

      Eval_t e3("+ x y");
      for (auto& k : e3.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e3({13,17}) << endl << endl;

      Eval_t e4("(+ x (- 10 y))");
      for (auto& k : e4.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e4({100, 50}) << endl << endl;

      const string expr_str = "(+ x (- (* (/ 3 t) y) 2))";
      Eval_t::Param_values v5 = {10, 50, 20};
      Eval_t e5(expr_str);
      for (auto& k : e5.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e5({50, 10, 20}) << endl;
      cout << endl << e5(Eval_t::Param_values{1,2,3}) << endl;
      cout << endl << e5(v5) << endl;
      cout << endl;

      Eval_t e6(expr_str, {"t", "x", "y"});
      for (auto& k : e6.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e6(v5) << endl;
      cout << endl;

      Eval_t::Param_keys k7 = {"t", "x", "y"};
      Eval_t e7(expr_str, k7);
      for (auto& k : e7.cparam_keys()) {
        cout << k << " ";
      }
      cout << endl << e7(v5) << endl;
      cout << endl;

      Expr ex1("+ 5.5 6.5 7 8");
      Eval_t e1ex1 = ex1.get_eval<double>();
      auto e2ex1 = ex1.get_eval<int>();
      cout << e1ex1({}) << endl;
      cout << e2ex1({}) << endl;
      cout << ex1.eval<short>({}) << endl;
      cout << Expr("- (* y 5 (/ x 3 2))").eval<float>({60, 5}, {"x", "y"}) << endl;
    }
    catch (const Error& e) {
        cerr << e << endl;
        throw;
    }

    cout << endl << "Success." << endl;

    // double arg1=1, arg2=2;
    // auto f = Expr_place::Eval<double>::bin_fs["+"];
    // cout << f(1,2) << endl;

    // auto f2 = bind(f, cref(arg1), cref(arg2));
    // cout << f2() << endl;
    // arg1=3, arg2=4;
    // cout << f2() << endl;

    // double *parg1=&arg1, *parg2=&arg2;
    // // auto f3 = bind(f, *parg1, *parg2);
    // auto f3 = bind(f, cref(*parg1), cref(*parg2));
    // // auto f3 = bind(f, *cref(parg1), *cref(parg2));
    // // auto f3 = bind(f, cref(*cref(parg1)), cref(*cref(parg2)));
    // cout << f3() << endl;
    // *parg1=10, *parg2=20;
    // cout << f3() << endl;
    // parg1=&arg1, parg2=&arg1;
    // cout << f3() << endl;

    // double &rarg1=arg1, &rarg2=arg2;
    // auto f4 = bind(f, cref(rarg1), cref(rarg2));
    // cout << f4() << endl;
    // rarg1=arg1, rarg2=arg1;
    // cout << f4() << endl;
    // arg1=1, arg2=2;
    // cout << f4() << endl;

    // using Pair = pair<const char*, int>;
    // // map<const char*, int> m = {{"1", 0}, {"2", 0}, {"3", 0}};
    // map<Pair::first_type, Pair::second_type> m = {{"1", 0}, {"2", 0}, {"3", 0}};
    // vector<int> v = {1, 2, 3};

    // // transform(m.begin(), m.end(), v.begin(), m.begin(),
    // transform(begin(m), end(m), begin(v), std::inserter(m, begin(m)),
    //           [](Pair pair, int i){ Pair p = make_pair(pair.first, i); cout << p.first << "-" << p.second << endl; return p; });

    // // Pair p = {"1",2};
    // // p = make_pair(p.first, 2);

    // for(const auto& p : m){
    //   cout << p.first << ":" << p.second << endl;
    // }

    // pair<vector<const char*>, vector<int>> pv = {{},vector<int>(1)};
    // pv.first = {"1", "2", "3"};
    // pv.second.reserve(3);
    // const int& cref = pv.second[1];
    // pv.second = {1, 2, 3};
    // cout << cref << endl;

    // using T = vector<int>;
    // unique_ptr<T> u1,u2;
    // u1 = make_unique<T>(T{1});
    // cout << u1.get() << endl;
    // u2 = move(u1);
    // cout << u2.get() << endl;

    // vector<int> v1 = {1,2,3,4};
    // cout << v1.data() << endl;
    // vector<int> v2;
    // v2 = move(v1);
    // cout << v2.data() << endl;

    return 0;
}
