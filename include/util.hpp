#ifndef ___UTIL_H_G73H38OD9843HG3048GH34JN0JNFG430
#define ___UTIL_H_G73H38OD9843HG3048GH34JN0JNFG430

#include "sos.hpp"

#include <map>
#include <algorithm>
#include <functional>

namespace SOS {
    using std::map;

    using std::function;
    using std::bind;

    using namespace std::placeholders;

    namespace Util {
        template <typename T> using Lazy = function<T()>;

        class Flag;

        template <typename Key, typename Value> class Const_map;

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
        template <typename Cont> bool equal(const Cont& cont);
    }

    class Util::Flag {
    public:
        Flag() = default;
        Flag(bool flag_)                         : _value(value_of(flag_)) { }

        bool is_valid() const             { return _value != Value::unknown; }
        bool is_set() const                   { return _value == Value::set; }
        void invalidate()                         { _value = Value::unknown; }
        void set(bool set_ = true)                { _value = value_of(set_); }
    private:
        enum class Value { unknown, set, unset };

        static Value value_of(bool set_);

        Value _value{Value::unknown};
    };

    template <typename Key, typename Value>
    class Util::Const_map {
    public:
        using Map = map<Key, Value>;

        Const_map(const Const_map& cmap)                            = default;
        Const_map& operator =(const Const_map& cmap)                = default;
        Const_map(Const_map&& cmap)                                 = default;
        Const_map& operator =(Const_map&& cmap)                     = default;
        Const_map(Map&& map_)                                 : _map(map_) { }
        Const_map(initializer_list<pair<const Key,
                                        Value>> list)         : _map{list} { }

        bool includes(const Key& key_) const noexcept;
        const Value& operator [](const Key& key_) const;
        const auto cbegin() const                { return std::cbegin(_map); }
        const auto cend() const                    { return std::cend(_map); }
        const auto begin() const                  { return std::begin(_map); }
        const auto end() const                      { return std::end(_map); }
        auto begin()                              { return std::begin(_map); }
        auto end()                                  { return std::end(_map); }
    private:
        Map _map;
    };
}

#include "util.tpp"

#endif // ___UTIL_H_G73H38OD9843HG3048GH34JN0JNFG430
