#include "sos.hpp"

using namespace SOS;

namespace Test {
    namespace Temp {
        template <typename Cont, typename ostream = std::ostream>
        ostream& operator <<(ostream& os, const Cont& rhs)
        {
            for (const auto& e : rhs) {
                os << e << " ";
            }
            return os;
        }

        template <typename Cont>
        bool operator ==(const Cont& lhs, const Cont& rhs)
        {
            return std::equal(std::begin(lhs), std::end(lhs),
                              std::begin(rhs));
        }
    }

    template <typename T>
    ostream& operator <<(ostream& os, const vector<T>& rhs)
        { return Temp::operator <<(os, rhs); }

    struct Dummy{};
    template <typename Params = Dummy, typename Output = string, typename Input = string>
    using TestCase = tuple<const Input, Params, const Output>;
    template <typename Params = Dummy, typename Output = string, typename Input = string>
    using TestData = vector<TestCase<Params, Output, Input>>;

    template <typename Output = string>
    void test_case(const Output& expect, const Output& res)
    {
        if (res == expect) return;
        ostringstream oss1, oss2;
        oss1 << expect;
        oss2 << res;
        throw Error("Mismatch: expected: '"s + oss1.str()
                    + "', got: '" + oss2.str() + "'");
    }

    template <typename Params = Dummy, typename Output = string, typename Input = string>
    void test(TestData<Params, Output, Input>& tdata,
              function<Output(const Input&, Params&)> f,
              const string& msg = "")
    try {
        if (!msg.empty()) {
            cout << "  " << string(msg.size()+16, '-') << "  " << endl;
            cout << "// Testing " << msg << " ...   \\\\" << endl;
        }
        for (auto& t : tdata) try {
            const Input& input = get<0>(t);
            Params& params = get<1>(t);
            const Output& expect = get<2>(t);
            const Output& res = f(input, params);
            test_case(expect, res);
        }
        catch (const Error& e) {
            cerr << "!! At input '" + get<0>(t) << "':" << endl;
            throw;
        }
        if (!msg.empty()) {
            cout << "\\\\ Testing " << msg << " done. //" << endl;
            cout << "  " << string(msg.size()+16, '-') << "  " << endl;
            cout << endl;
        }
    }
    catch (const Error& e) {
        cerr << "!! " << e << " !!" << endl;
        throw;
    }
}
