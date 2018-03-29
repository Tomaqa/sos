#include "sos.h"
#include "parser.h"

using namespace SOS;

void test(const string& res, const string& expect)
{
    if (res == expect) return;
    throw Error("Mismatch: expected: '"s + expect + "', got: '" + res + "'");
}

void flat_extract_braces_test(istringstream&& iss, const string& expect)
{
    test(Parser::flat_extract_braces(move(iss)).str(), expect);
}

void test_expr(const string& str, const string& expect, bool to_binary = false)
{
    Parser::Exprs exprs(str);
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

    auto f = Parser::f_oper<double>["+"];

    return 0;
}
