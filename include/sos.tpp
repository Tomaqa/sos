namespace SOS {

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

    template <typename T1, typename T2>
    string to_string(const pair<T1, T2>& rhs)
    {
        return to_string(rhs.first) + " " + to_string(rhs.second);
    }
}
