#ifndef ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
#define ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430

#include <cstdlib>
#include <string>
#include <vector>
#include <iostream>
#include <sstream>
#include <iterator>
#include <algorithm>
#include <regex>

using std::move;
using std::string;
using std::vector;
using std::pair;
using std::ostream;
using std::istringstream;
using std::find;
using std::begin;
using std::end;
using std::regex;

using namespace std::string_literals;

namespace SOS {
    namespace ODE {
        using Time = double;
        template <typename T>
        using Interval = pair<T,T>;
        using Value = double;
        using State = vector<Value>;

        constexpr const char* re_float = "[+-]?\\d*\\.?\\d+";

        class Error {
        public:
            Error(const string& msg = "") : _msg(msg) { }

            friend ostream& operator <<(ostream& os, const Error& rhs)
              { return (os << rhs); }
        private:
            string _msg;
        };
    }
}

#endif // ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
