#include <algorithm>

namespace SOS {
    using namespace Util;
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
    bool Util::all_of(const Cont& cont, Un_f f)
    {
        return std::all_of(std::begin(cont), std::end(cont), std::move(f));
    }

    template <typename Cont, typename Un_f>
    bool Util::any_of(const Cont& cont, Un_f f)
    {
        return std::any_of(std::begin(cont), std::end(cont), std::move(f));
    }

    template <typename Cont, typename Un_f>
    bool Util::none_of(const Cont& cont, Un_f f)
    {
        return std::none_of(std::begin(cont), std::end(cont), std::move(f));
    }

    template <typename Cont, typename Bin_f>
    bool Util::all_equal(const Cont& cont, Bin_f f)
    {
        const auto& e0 = cont.front();
        return all_of(cont, [&e0, &f](const auto& e){ return f(e0, e); });
    }

    template <typename Cont1, typename InputIt2, typename Bin_f>
    bool Util::equal(const Cont1& cont1, InputIt2 first2, Bin_f f)
    {
        return std::equal(std::begin(cont1), std::end(cont1),
                          first2,
                          std::move(f));
    }

    template <typename Cont, typename T>
    auto Util::find(const Cont& cont, const T& value)
    {
        return std::find(std::begin(cont), std::end(cont), value);
    }

    template <typename Cont, typename Un_f>
    auto Util::find_if(const Cont& cont, Un_f f)
    {
        return std::find_if(std::begin(cont), std::end(cont), f);
    }

    template <typename Cont, typename T>
    bool Util::includes(const Cont& cont, const T& value)
    {
        return find(cont, value) != std::end(cont);
    }

    template <typename Cont, typename Un_f>
    Un_f Util::for_each(Cont& cont, Un_f f)
    {
        return std::for_each(std::begin(cont),
                             std::end(cont),
                             std::move(f));
    }

    template <typename Cont, typename Un_f>
    Un_f Util::for_each(Cont&& cont, Un_f f)
    {
        return std::for_each(std::make_move_iterator(std::begin(cont)),
                             std::make_move_iterator(std::end(cont)),
                             std::move(f));
    }

    template <typename Cont1, typename InputIt2, typename Bin_f>
    Bin_f Util::for_each(Cont1& cont1, InputIt2 first2, Bin_f f)
    {
        for (auto first1 = std::begin(cont1), last1 = std::end(cont1);
             first1 != last1; ++first1, ++first2) {
            f(*first1, forward<typename InputIt2::reference>(*first2));
        }
        return std::move(f);
    }

    template <typename Cont1, typename InputIt2, typename Bin_f>
    Bin_f Util::for_each(Cont1&& cont1, InputIt2 first2, Bin_f f)
    {
        for (auto first1 = std::make_move_iterator(std::begin(cont1)),
             last1 = std::make_move_iterator(std::end(cont1));
             first1 != last1; ++first1, ++first2) {
            f(move(*first1), forward<typename InputIt2::reference>(*first2));
        }
        return std::move(f);
    }

    template <typename Cont, typename OutputIt>
    OutputIt Util::copy(const Cont& cont, OutputIt d_first)
    {
        return std::copy(std::begin(cont),
                         std::end(cont),
                         d_first);
    }

    template <typename Cont, typename OutputIt>
    OutputIt Util::move(Cont&& cont, OutputIt d_first)
    {
        return std::move(std::begin(cont),
                         std::end(cont),
                         d_first);
    }

    template <typename Cont, typename OutputIt, typename Un_f>
    OutputIt Util::transform(Cont& cont, OutputIt d_first, Un_f f)
    {
        return std::transform(std::begin(cont),
                              std::end(cont),
                              d_first,
                              std::move(f));
    }

    template <typename Cont, typename OutputIt, typename Un_f>
    OutputIt Util::transform(Cont&& cont, OutputIt d_first, Un_f f)
    {
        return std::transform(std::make_move_iterator(std::begin(cont)),
                              std::make_move_iterator(std::end(cont)),
                              d_first,
                              std::move(f));
    }

    template <typename Cont1, typename InputIt2,
              typename OutputIt, typename Bin_f>
    OutputIt Util::transform(Cont1& cont1, InputIt2 first2,
                       OutputIt d_first, Bin_f f)
    {
        return std::transform(std::begin(cont1),
                              std::end(cont1),
                              first2,
                              d_first,
                              std::move(f));
    }

    template <typename Cont1, typename InputIt2,
              typename OutputIt, typename Bin_f>
    OutputIt Util::transform(Cont1&& cont1, InputIt2 first2,
                       OutputIt d_first, Bin_f f)
    {
        return std::transform(std::make_move_iterator(std::begin(cont1)),
                              std::make_move_iterator(std::end(cont1)),
                              first2,
                              d_first,
                              std::move(f));
    }

    template <typename OutputCont, typename InputIt, typename Un_f>
    OutputCont Util::split_if(InputIt first, InputIt last, Un_f f)
    {
        OutputCont d_cont;
        if (first == last) return d_cont;
        auto first2 = first;
        for (++first2; first2 != last; ++first2) {
            if (!f(*first2)) continue;
            d_cont.emplace_back(std::make_move_iterator(first),
                                std::make_move_iterator(first2));
            first = first2;
        }
        if (first != first2) {
            d_cont.emplace_back(std::make_move_iterator(first),
                                std::make_move_iterator(first2));
        }
        return d_cont;
    }

    template <typename OutputCont, typename InputCont, typename Un_f>
    OutputCont Util::split_if(InputCont&& cont, Un_f f)
    {
        return split_if<OutputCont>(std::begin(cont), std::end(cont), f);
    }

    template <typename OutputCont, typename InputCont, typename Un_f>
    OutputCont Util::inplace_split_if(InputCont& cont, Un_f f)
    {
        if (cont.empty()) return OutputCont();
        auto last = std::end(cont);
        auto first = std::find_if(++std::begin(cont), last, f);
        OutputCont d_cont = split_if<OutputCont>(first, last, f);
        cont.erase(first, last);
        return d_cont;
    }

    template <typename T>
    vector<T>& Util::operator +=(vector<T>& lhs, const vector<T>& rhs)
    {
        for_each(lhs, std::begin(rhs),
                 [](T& l, const T& r){ l += r; });
        return lhs;
    }

    template <typename T>
    vector<T> Util::operator +(vector<T> lhs, const vector<T>& rhs)
    {
        return (lhs += rhs);
    }

    template <typename T>
    vector<T>& Util::operator *=(vector<T>& lhs, const T& rhs)
    {
        for_each(lhs, [&rhs](T& l){ l *= rhs; });
        return lhs;
    }

    template <typename T>
    vector<T> Util::operator *(vector<T> lhs, const T& rhs)
    {
        return (lhs *= rhs);
    }

    template <typename T>
    vector<T> Util::operator *(const T& lhs, vector<T> rhs)
    {
        return (rhs *= lhs);
    }
}

