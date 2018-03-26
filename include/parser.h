#ifndef ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
#define ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430

#include "sos.h"

#include <regex>

using std::regex;
using std::regex_match;

namespace SOS {
    namespace Parser {
        constexpr const char* re_float = "[+-]?\\d*\\.?\\d+";
        template <typename Arg, typename F>
        const map<const char, F> oper = {
            {'+', [](Arg a, Arg b){ return a + b; }},
            {'-', [](Arg a, Arg b){ return a - b; }},
            {'*', [](Arg a, Arg b){ return a * b; }},
            {'/', [](Arg a, Arg b){ return a / b; }},
        };
        // std::function

        istringstream flat_extract_brackets(istringstream & iss);
        auto parse_expr(const string& expr);
    }
}

#endif // ___SOS_PARSER_H_OUDH983489GH43G3454H8J540H45T938HJ3409FG430
