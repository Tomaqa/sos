#ifndef ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
#define ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430

#include <cstdlib>
#include <cstring>
#include <cassert>

#include <string>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <memory>
#include <algorithm>
#include <functional>

using std::move;
using std::forward;

using std::vector;
using std::make_pair;
using std::map;
using std::initializer_list;

using std::pair;
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

using std::for_each;
using std::distance;

using std::function;
using std::bind;

using namespace std::string_literals;

namespace SOS {
    template <typename T>
    using Lazy = function<T()>;

    class Error {
    public:
        Error(const string& msg_ = "") : _msg(msg_) { }

        friend ostream& operator <<(ostream& os, const Error& rhs)
            { return (os << rhs._msg); }
    private:
        string _msg;
    };

    template <typename Key, typename Value>
    class Const_map {
    public:
        using Map = map<Key, Value>;

        Const_map(const Const_map& cmap) = default;
        Const_map& operator =(const Const_map& cmap) = default;
        Const_map(Const_map&& cmap) = default;
        Const_map& operator =(Const_map&& cmap) = default;
        Const_map(Map&& map_) : _map(map_) { }
        Const_map(initializer_list<pair<const Key, Value>> list)
            : _map{list} { }

        bool includes(const Key& key_) const noexcept
            { return _map.count(key_) == 1; }
        const Value& operator [](const Key& key_) const
            { return _map.at(key_); }
        const auto cbegin() const { return std::cbegin(_map); }
        const auto cend() const { return std::cend(_map); }
        const auto begin() const { return std::begin(_map); }
        const auto end() const { return std::end(_map); }
        auto begin() { return std::begin(_map); }
        auto end() { return std::end(_map); }
    private:
        Map _map;
    };

    #define expect(condition, msg) if (!(condition)) throw Error(msg);
}

namespace std {
    template <typename T>
    inline string to_string(const vector<T>& rhs)
    {
        string str("");
        for (const auto& e : rhs) {
            str += to_string(e) + " ";
        }
        return move(str);
    }

    inline const string& to_string(const string& rhs)
        { return rhs; }
}

#endif // ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
