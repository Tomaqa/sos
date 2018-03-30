#ifndef ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
#define ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430

#include <cstdlib>
#include <cstring>

#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <iostream>
#include <sstream>
#include <memory>
#include <iterator>
#include <algorithm>

using std::move;
using std::swap;
using std::ref;
using std::cref;

using std::vector;
using std::make_pair;
using std::map;
using std::unordered_map;
using std::initializer_list;

using std::pair;
using std::get;

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
using std::iterator;
using std::begin;
using std::end;
using std::cbegin;
using std::cend;
using std::distance;
using std::transform;
using std::copy;

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

    template <typename Key, typename Value>
    class Const_map {
    public:
        using Map = map<Key, Value>;

        Const_map(Map&& map) : _map(map) { }
        Const_map(initializer_list<pair<const Key, Value>> list)
            : _map{list} { }

        bool includes(const Key& key) const noexcept
            { return _map.count(key) == 1; }
        const Value& operator [] (const Key& key) const
            { return _map.at(key); }
        auto begin() { return _map.begin(); }
        const auto begin() const { return _map.begin(); }
        auto end() { return _map.end(); }
        const auto end() const { return _map.end(); }
    private:
        Map _map;
    };
}

#endif // ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
