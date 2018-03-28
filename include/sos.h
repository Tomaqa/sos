#ifndef ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
#define ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430

#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <memory>
#include <iterator>
#include <algorithm>

using std::move;

using std::vector;
using std::pair;
using std::make_pair;
using std::map;

using std::cout;
using std::cerr;
using std::endl;

using std::string;
using std::to_string;
using std::ostream;
using std::ostringstream;
using std::istringstream;

using std::unique_ptr;
using std::make_unique;
using std::shared_ptr;
using std::make_shared;

using std::find;
using std::for_each;
using std::begin;
using std::end;

using namespace std::string_literals;

namespace SOS {
    class Error {
    public:
        Error(const string& msg = "") : _msg(msg) { }

        friend ostream& operator <<(ostream& os, const Error& rhs)
            { return (os << rhs._msg); }
    private:
        string _msg;
    };
}

#endif // ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
