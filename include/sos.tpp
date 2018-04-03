namespace SOS {
    class Error {
    public:
        Error(const string& msg_ = "") : _msg(msg_) { }

        explicit operator string () const
            { return _msg; }
        friend const string& to_string(const Error& rhs)
            { return rhs._msg; }
        friend ostream& operator <<(ostream& os, const Error& rhs)
            { return (os << to_string(rhs)); }
        Error operator +(const string& rhs) const
            { return Error(_msg + rhs); }
        friend Error operator +(const string& lhs, const Error& rhs)
            { return Error(lhs + rhs._msg); }
        Error& operator +=(const string& rhs)
            { _msg += rhs; return *this; }
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

    class Flag {
    public:
        Flag() = default;
        Flag(bool flag_) : _value(value_of(flag_)) { }

        bool is_valid() const
            { return _value != Value::unknown; }
        bool is_set() const
            { return _value == Value::set; }
        void invalidate()
            { _value = Value::unknown; }
        void set(bool set_ = true)
            { _value = value_of(set_); }
    private:
        enum class Value { unknown, set, unset };

        static Value value_of(bool set_)
            { return set_ ? Value::set : Value::unset; }

        Value _value{Value::unknown};
    };

    template <typename Cont, typename Un_f>
    Un_f for_each(Cont& cont, Un_f f)
    {
        return move(std::for_each(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename Un_f>
    bool all_of(const Cont& cont, Un_f f)
    {
        return move(std::all_of(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename Un_f>
    bool any_of(const Cont& cont, Un_f f)
    {
        return move(std::any_of(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename OutputIt, typename Un_f>
    OutputIt transform(Cont& cont, OutputIt d_first, Un_f f)
    {
        return move(std::transform(std::begin(cont), std::end(cont),
                                   move(d_first),
                                   move(f)));
    }

    template <typename Cont1, typename InputIt2,
              typename OutputIt, typename Bin_f>
    OutputIt transform(Cont1& cont1, InputIt2 first2,
                       OutputIt d_first, Bin_f f)
    {
        return move(std::transform(std::begin(cont1), std::end(cont1),
                                   move(first2),
                                   move(d_first),
                                   move(f)));
    }
}

namespace std {
    template <typename T>
    string to_string(const vector<T>& rhs)
    {
        string str("");
        for (const auto& e : rhs) {
            str += to_string(e) + " ";
        }
        return move(str);
    }
}
