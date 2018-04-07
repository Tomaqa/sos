#pragma once

#include <cstdlib>
#include <cstring>
#include <cmath>

#include <string>
#include <vector>
#include <iostream>
#include <sstream>
#include <memory>
#include <utility>

namespace SOS {
    using std::move;
    using std::forward;

    using std::vector;
    using std::initializer_list;

    using std::pair;
    using std::make_pair;
    using std::tuple;
    using std::get;
    using std::tie;

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

    using namespace std::string_literals;

    class Error;

    #define expect(condition, msg) if (!(condition)) throw Error(msg);

    template <typename T> string to_string(const vector<T>& rhs);
    template <typename T1, typename T2>
        string to_string(const pair<T1, T2>& rhs);
    template <typename... Args>
        string to_string(const tuple<Args...>& rhs);
    inline const string& to_string(const string& rhs)          { return rhs; }

    template <typename T>
        ostream& operator <<(ostream& os, const vector<T>& rhs);
    template <typename T1, typename T2>
        ostream& operator <<(ostream& os, const pair<T1, T2>& rhs);
    template <typename... Args>
        ostream& operator <<(ostream& os, const tuple<Args...>& rhs);
}

namespace SOS {
    class Error {
    public:
        Error(const string& msg_ = "") : _msg(msg_) { }

        explicit operator string () const                     { return _msg; }
        friend const string& to_string(const Error& rhs)  { return rhs._msg; }
        friend ostream& operator <<(ostream& os, const Error& rhs);
        Error operator +(const string& rhs) const;
        friend Error operator +(const string& lhs, const Error& rhs);
        Error& operator +=(const string& rhs);
    private:
        string _msg;
        mutable bool _printed{false};
    };
}

#include "sos.tpp"
