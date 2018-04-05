#include "sos.hpp"
#include "util.hpp"

namespace SOS {
    using namespace Util;

    namespace Test {

        struct Dummy{};
        template <typename Params, typename Output, typename Input>
        using Test_case = tuple<const Input, Params, const Output>;
        template <typename Params = Dummy,
                  typename Output = string, typename Input = string>
        using Test_data = vector<Test_case<Params, Output, Input>>;
        template <typename Params, typename Output, typename Input>
        using Res_f = function<Output(const Input&, bool, Params&)>;
        template <typename Output>
        using Pred_f = function<bool(const Output&, const Output&)>;

        template <typename Output>
        void test_pred(const Output& expect_, const Output& res,
                       Pred_f<Output> pred, const string& pred_msg)
        {
            expect(pred(res, expect_),
                   "Condition 'res "s + pred_msg + " expect' not met: "
                   +"expected: '" + to_string(expect_)
                   + "', got: '" + to_string(res) + "'");
        }

        template <typename Params = Dummy,
                  typename Output = string, typename Input = string>
        void test(Test_data<Params, Output, Input>& tdata,
                  Res_f<Params, Output, Input> f,
                  const string& msg = "",
                  bool should_throw = false,
                  Pred_f<Output> pred = std::equal_to<Output>(),
                  const string& pred_msg = "==")
        {
            Input input;
            try {
                string head_msg, tail_msg, line;
                if (!msg.empty()) {
                    head_msg = "// Testing "s + msg
                               + " with " + (should_throw ? "in" : "")
                               + "valid inputs"
                               + "...   \\\\";
                    line = "  " + string(head_msg.size()-4, '-') + "  ";
                    cout << line << endl
                         << head_msg << endl;
                }
                for (auto& t : tdata) try {
                    input = get<0>(t);
                    Params& params = get<1>(t);
                    const Output& expect_ = get<2>(t);
                    const Output& res = f(input, should_throw, params);
                    if (should_throw) {
                        throw Dummy();
                    }
                    test_pred<Output>(expect_, res, pred, pred_msg);
                }
                catch (const Error& e) {
                    if (should_throw) continue;
                    throw;
                }
                catch (const Dummy& e) {
                    throw Error("Expected thrown exception");
                }
                if (!msg.empty()) {
                    tail_msg = "\\\\ Testing " + msg + " done.";
                    tail_msg += string(head_msg.size() - tail_msg.size() - 3,
                                       ' ')
                             + " //";
                    cout << tail_msg << endl
                         << line << endl << endl;
                }
            }
            catch (const Error& e) {
                cerr << "!! At input '" << to_string(input) << "':" << endl;
                cerr << "!! " << e << " !!" << endl;
                throw;
            }
        }
    }
}
