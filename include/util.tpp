namespace SOS {
    template <typename Key, typename Value>
    class Util::Const_map {
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

    template <typename Cont, typename Un_f>
    Un_f Util::for_each(Cont& cont, Un_f f)
    {
        return move(std::for_each(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename Un_f>
    bool Util::all_of(const Cont& cont, Un_f f)
    {
        return move(std::all_of(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename Un_f>
    bool Util::any_of(const Cont& cont, Un_f f)
    {
        return move(std::any_of(std::begin(cont), std::end(cont), move(f)));
    }

    template <typename Cont, typename OutputIt, typename Un_f>
    OutputIt Util::transform(Cont& cont, OutputIt d_first, Un_f f)
    {
        return move(std::transform(std::begin(cont), std::end(cont),
                                   move(d_first),
                                   move(f)));
    }

    template <typename Cont1, typename InputIt2,
              typename OutputIt, typename Bin_f>
    OutputIt Util::transform(Cont1& cont1, InputIt2 first2,
                       OutputIt d_first, Bin_f f)
    {
        return move(std::transform(std::begin(cont1), std::end(cont1),
                                   move(first2),
                                   move(d_first),
                                   move(f)));
    }

    template <typename Cont>
    bool Util::equal(const Cont& cont)
    {
        const auto& e0 = cont.front();
        return all_of(cont, [&e0](const auto& e){ return e == e0; });
    }
}
