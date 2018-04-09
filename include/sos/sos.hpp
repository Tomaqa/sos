#pragma once

#include <iosfwd>
#include <string>
#include <vector>
#include <utility>

namespace SOS {
    using std::move;
    using std::forward;

    using std::ostream;
    using std::istream;
    using std::istringstream;
    using std::ostringstream;

    using std::string;
    using std::to_string;
    using namespace std::string_literals;

    using std::vector;
    using std::initializer_list;

    using std::pair;
    using std::tuple;
    using std::get;
    using std::make_pair;

    class Error;

    #define expect(condition, msg) if (!(condition)) throw Error(msg);

    template <typename T> string to_string(const vector<T>& rhs);
    template <typename T1, typename T2>
        string to_string(const pair<T1, T2>& rhs);
    template <typename... Args>
        string to_string(const tuple<Args...>& rhs);
    inline const string& to_string(const string& rhs)          { return rhs; }
    string to_string(istream& rhs);

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
