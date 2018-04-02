#include "sos.hpp"

using namespace SOS;

namespace Test {
    struct Dummy{};
    template <typename Params = Dummy, typename Output = string, typename Input = string>
    using TestCase = tuple<const Input, Params, const Output>;
    template <typename Params = Dummy, typename Output = string, typename Input = string>
    using TestData = vector<TestCase<Params, Output, Input>>;

    template <typename Output = string>
    void test_case(const Output& expect_, const Output& res)
    {
        expect(res == expect_,
               "Mismatch: expected: '"s + to_string(expect_)
                + "', got: '" + to_string(res) + "'");
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
            const Output& expect_ = get<2>(t);
            const Output& res = f(input, params);
            test_case(expect_, res);
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
