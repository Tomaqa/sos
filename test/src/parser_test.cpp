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

void test_expr(const string& str, const string& expect)
{
    test((string)Parser::Exprs(str), expect);
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
      test_expr("((()))", "( ( ) )");
      test_expr("0(1(2(3)4)5)6", "( 0 ( 1 ( 2 3 4 ) 5 ) 6 )");
      test_expr("1 (+ 2 (3))",    "( 1 ( + 2 3 ) )");
      // test_expr("(1) (+ 2 (3))",    "( 1 ( + 2 3 ) )");
      // test_expr(" (1 2 3)", "( 1 2 3 )");
    }
    catch (const Error& e) {
        cerr << e << endl;
        throw;
    }

    return 0;
}
