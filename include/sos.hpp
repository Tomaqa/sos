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

namespace SOS {
    using std::move;
    using std::forward;

    using std::vector;
    using std::map;
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

    using std::function;
    using std::bind;

    using namespace std::string_literals;
    using namespace std::placeholders;

    template <typename T>
    using Lazy = function<T()>;

    class Error;

    template <typename Key, typename Value>
    class Const_map;

    class Flag;

    #define expect(condition, msg) if (!(condition)) throw Error(msg);

    template <typename Cont, typename Un_f>
    Un_f for_each(Cont& cont, Un_f f);
    template <typename Cont, typename Un_f>
    bool all_of(const Cont& cont, Un_f f);
    template <typename Cont, typename Un_f>
    bool any_of(const Cont& cont, Un_f f);
    template <typename Cont, typename OutputIt, typename Un_f>
    OutputIt transform(Cont& cont, OutputIt d_first, Un_f f);
    template <typename Cont1, typename InputIt2,
              typename OutputIt, typename Bin_f>
    OutputIt transform(Cont1& cont1, InputIt2 first2,
                       OutputIt d_first, Bin_f f);
}

namespace std {
    template <typename T>
    string to_string(const vector<T>& rhs);

    inline const string& to_string(const string& rhs)
        { return rhs; }
}

#include "sos.tpp"

#endif // ___SOS_H_G73H38ODIHG5GH54GT95H8J549JFG430
