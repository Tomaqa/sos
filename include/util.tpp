namespace SOS {
    template <typename Key, typename Value>
    bool Util::Const_map<Key, Value>::includes(const Key& key_) const noexcept
    {
        return _map.count(key_) == 1;
    }

    template <typename Key, typename Value>
    const Value& Util::Const_map<Key, Value>
        ::operator [](const Key& key_) const
    {
        return _map.at(key_);
    }

    ///////////////////////////////////////////////////////////////

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

    template <typename Cont, typename Un_f>
    bool Util::none_of(const Cont& cont, Un_f f)
    {
        return move(std::none_of(std::begin(cont), std::end(cont), move(f)));
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

    template <typename Cont, typename Bin_f>
    bool Util::equal(const Cont& cont, Bin_f f)
    {
        const auto& e0 = cont.front();
        return all_of(cont, [&e0, &f](const auto& e){ return f(e, e0); });
    }

    template <typename Cont1, typename Cont2, typename Bin_f>
    bool Util::equal(const Cont1& cont1, const Cont2& cont2, Bin_f f)
    {
        return std::equal(std::begin(cont1), std::end(cont1),
                          std::begin(cont2),
                          move(f));
    }
}