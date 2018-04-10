namespace SOS {
    namespace Aux {
        template<size_t...> struct Seq{};

        template<size_t n, size_t... is>
        struct Gen_seq : Gen_seq<n-1, n-1, is...>{};

        template<size_t... is>
        struct Gen_seq<0, is...> : Seq<is...>{};

        template<typename Tuple, size_t... is>
        static void tuple_to_string(string& str, const Tuple& t, Seq<is...>)
        {
            using A = int[];
            A{0, (void(str += (is == 0? "" : " ")
                           + to_string(get<is>(t))
                      ), 0)...};
        }
    }

    template <typename T>
    string to_string(const vector<T>& rhs)
    {
        string str("");
        for (const auto& e : rhs) {
            str += to_string(e) + " ";
        }
        return move(str);
    }

    template <typename Key, typename Value>
    string to_string(const map<Key, Value>& rhs)
    {
        string str("");
        for (const auto& e : rhs) {
            str += to_string(e) + ", ";
        }
        return move(str);
    }

    template <typename T1, typename T2>
    string to_string(const pair<T1, T2>& rhs)
    {
        return to_string(rhs.first) + " " + to_string(rhs.second);
    }

    template<typename... Args>
    string to_string(const tuple<Args...>& rhs)
    {
      string str("");
      Aux::tuple_to_string(str, rhs, Aux::Gen_seq<sizeof...(Args)>());
      return move(str);
    }

    template <typename T>
    ostream& operator <<(ostream& os, const vector<T>& rhs)
    {
        return (os << to_string(rhs));
    }

    template <typename Key, typename Value>
    ostream& operator <<(ostream& os, const map<Key, Value>& rhs)
    {
        return (os << to_string(rhs));
    }

    template <typename T1, typename T2>
    ostream& operator <<(ostream& os, const pair<T1, T2>& rhs)
    {
        return (os << to_string(rhs));
    }

    template <typename... Args>
    ostream& operator <<(ostream& os, const tuple<Args...>& rhs)
    {
        return (os << to_string(rhs));
    }
}
