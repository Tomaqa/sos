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
    test(Expr::flat_extract_braces(move(iss)).str(), expect);
}

void test_expr(const string& str, const string& expect, bool to_binary = false)
{
    Exprs exprs(str);
    if (to_binary) exprs.to_binary();
    test((string)exprs, expect);
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
    }
    catch (const Error& e) {
        cerr << e << endl;
        throw;
    }

    cout << "Success." << endl;

    double arg1=1, arg2=2;
    auto f = Expr::Eval<double>::bin_fs["+"];
    cout << f(1,2) << endl;

    auto f2 = bind(f, cref(arg1), cref(arg2));
    cout << f2() << endl;
    arg1=3, arg2=4;
    cout << f2() << endl;

    double *parg1=&arg1, *parg2=&arg2;
    // auto f3 = bind(f, *parg1, *parg2);
    auto f3 = bind(f, cref(*parg1), cref(*parg2));
    // auto f3 = bind(f, *cref(parg1), *cref(parg2));
    // auto f3 = bind(f, cref(*cref(parg1)), cref(*cref(parg2)));
    cout << f3() << endl;
    *parg1=10, *parg2=20;
    cout << f3() << endl;
    parg1=&arg1, parg2=&arg1;
    cout << f3() << endl;

    double &rarg1=arg1, &rarg2=arg2;
    auto f4 = bind(f, cref(rarg1), cref(rarg2));
    cout << f4() << endl;
    rarg1=arg1, rarg2=arg1;
    cout << f4() << endl;
    arg1=1, arg2=2;
    cout << f4() << endl;

    Expr::Eval<double> op("123");

    return 0;
}
