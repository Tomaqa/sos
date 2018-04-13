#pragma once

#include "sos.hpp"

#include <functional>

namespace SOS {
    using std::function;
    using namespace std::placeholders;

    namespace Util {
        template <typename T> using Lazy = function<T()>;

        template <typename T> using Stream_ptr = T*;

        class Flag;

        template <typename Key, typename Value> class Const_map;

        template <typename Cont, typename Un_f>
            Un_f for_each(Cont&& cont, Un_f f);
        template <typename Cont1, typename InputIt2, typename Bin_f>
            Bin_f for_each(Cont1&& cont1, InputIt2 first2, Bin_f f);
        template <typename Cont, typename Un_f>
            bool all_of(const Cont& cont, Un_f f);
        template <typename Cont, typename Un_f>
            bool any_of(const Cont& cont, Un_f f);
        template <typename Cont, typename Un_f>
            bool none_of(const Cont& cont, Un_f f);
        template <typename Cont, typename OutputIt>
            OutputIt copy(Cont&& cont, OutputIt d_first);
        template <typename Cont, typename OutputIt, typename Un_f>
            OutputIt transform(Cont&& cont, OutputIt d_first, Un_f f);
        template <typename Cont1, typename InputIt2,
                  typename OutputIt, typename Bin_f>
            OutputIt transform(Cont1&& cont1, InputIt2 first2,
                               OutputIt d_first, Bin_f f);
        template <typename Cont,
                  typename Bin_f = std::equal_to<typename Cont::value_type>>
            bool all_equal(const Cont& cont, Bin_f f = Bin_f());
        template <typename Cont1, typename InputIt2,
                  typename Bin_f = std::equal_to<typename Cont1::value_type>>
            bool equal(const Cont1& cont1, InputIt2 first2,
                       Bin_f f = Bin_f());

        template <typename T>
            vector<T>& operator +=(vector<T>& lhs, vector<T> rhs);
        template <typename T>
            vector<T> operator +(vector<T> lhs, vector<T> rhs);
        template <typename T>
            vector<T>& operator *=(vector<T>& lhs, T rhs);
        template <typename T>
            vector<T> operator *(vector<T> lhs, T rhs);
        template <typename T>
            vector<T> operator *(T lhs, vector<T> rhs);

        Stream_ptr<istream> run_get_istream(int argc, const char* argv[]);
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
