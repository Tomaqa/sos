#include "parser.h"

namespace SOS {
    namespace Parser {
        istringstream flat_extract_brackets(istringstream & iss)
        {
            string str;
            iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
            getline(iss, str, ')');
            return istringstream(str);
        }

        auto parse_expr(const string& expr)
        {
            regex re("\\s*(\\(.*\\)|[^()]*)\\s*");
            if (!regex_match(expr, re)) {
                throw Error("Invalid format of input expression: " + expr);
            }

        }
    }
}
