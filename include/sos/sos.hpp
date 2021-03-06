#pragma once

#include <iosfwd>
#include <string>
#include <vector>
#include <map>
#include <utility>

namespace SOS {
    using std::move;
    using std::forward;

    using std::ostream;
    using std::istream;
    using std::ofstream;
    using std::ifstream;
    using std::stringstream;
    using std::istringstream;
    using std::ostringstream;
    using std::streampos;

    using std::string;
    using namespace std::string_literals;

    using std::vector;
    using std::initializer_list;

    using std::map;

    using std::pair;
    using std::tuple;
    using std::get;
    using std::make_pair;

    class Error;

    constexpr const int float_precision = 6;
    constexpr const int double_precision = 10;

    #define expect(condition, msg) if (!(condition)) throw Error(msg);

    string to_string(char arg);
    string to_string(int arg);
    string to_string(long arg);
    string to_string(unsigned arg);
    string to_string(unsigned long arg);
    string to_string(float arg);
    string to_string(double arg);
    template <typename T>
        string to_string(const vector<T>& rhs);
    template <typename Key, typename Value>
        string to_string(const map<Key, Value>& rhs);
    template <typename T1, typename T2>
        string to_string(const pair<T1, T2>& rhs);
    template <typename... Args>
        string to_string(const tuple<Args...>& rhs);
    inline const string& to_string(const string& rhs)          { return rhs; }
    string to_string(istream& rhs);

    int istream_remain_size(istream& is);

    template <typename T>
        ostream& operator <<(ostream& os, const vector<T>& rhs);
    template <typename Key, typename Value>
        ostream& operator <<(ostream& os, const map<Key, Value>& rhs);
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
