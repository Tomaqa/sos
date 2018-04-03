#include "test.hpp"
#include "ode/solver.hpp"
#include "ode/euler.hpp"

namespace SOS {
    namespace Test {
        using namespace ODE;
        using Context = Solver::Context;

        /////////////////////////////////////////////////////////////////

        Context context_res(const string& input, bool, Dummy&)
        {
            return Context(input);
        }

        /////////////////////////////////////////////////////////////////

        using Param_keys = Solver::Param_keys;
        using Unified_output = pair<bool, Param_keys>;

        Unified_output unified_res(const Euler& solver, bool, Dummy&)
        {
            Param_keys param_keys_;
            bool unified = solver.is_unified();
            if (unified) param_keys_ = solver.cunif_param_keys();
            return Unified_output(unified, param_keys_);
        }

        /////////////////////////////////////////////////////////////////
    }
}


/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
{
    using namespace SOS;
    using namespace SOS::Test;
    using namespace std;

    Test_data<Dummy, Context> context_data = {
        {"( (0 10) (0))",                                            {},        {{0, 10}, {0}}                                               },
        {" ( (0 10) (0)) ",                                          {},        {{0, 10}, {0}}                                               },
        {" ((0 10) (0) ) ",                                          {},        {{0, 10}, {0}}                                               },
        {" (0 10) (0)",                                              {},        {{0, 10}, {0}}                                               },
        {"   ( -5.0 10.5 )  ( 0 1.1 2 )  ",                          {},        {{-5, 10.5}, {0, 1.1, 2}}                                    },
        {"   (5.0 10.5 )( 0 1.1 2)  ",                               {},        {{5, 10.5}, {0, 1.1, 2}}                                     },
        {" ( 5.0 10.5)  (0 1.1 2 )  ",                               {},        {{5, 10.5}, {0, 1.1, 2}}                                     },
        {" (0 1)()",                                                 {},        {{0, 1}, {}}                                                 },
        {" (0.546654100  1163)  (  231 1531.513   1543.35 -44)",     {},        {{0.546654100, 1163}, {231, 1531.513, 1543.35, -44}}         },
    };

    Test_data<Dummy, Context> context_throw_data = {
        {"",                                                         {},        {{0, 10}, {0}}                                               },
        {"0",                                                        {},        {{0, 10}, {0}}                                               },
        {"0 10",                                                     {},        {{0, 10}, {0}}                                               },
        {"0 10 0",                                                   {},        {{0, 10}, {0}}                                               },
        {"(0 10 0)",                                                 {},        {{0, 10}, {0}}                                               },
        {"(0 10) 0",                                                 {},        {{0, 10}, {0}}                                               },
        {"( 10) (0)",                                                {},        {{0, 10}, {0}}                                               },
        {"() (0)",                                                   {},        {{0, 10}, {0}}                                               },
        {"0 10 (0)",                                                 {},        {{0, 10}, {0}}                                               },
        {"(0 10 (0))",                                               {},        {{0, 10}, {0}}                                               },
        {"(0 10(0))",                                                {},        {{0, 10}, {0}}                                               },
        {"((0 10(0)))",                                              {},        {{0, 10}, {0}}                                               },
        {"(x 10)(0)",                                                {},        {{0, 10}, {0}}                                               },
        {"(0 x)(0)",                                                 {},        {{0, 10}, {0}}                                               },
        {"(0 10)(x)",                                                {},        {{0, 10}, {0}}                                               },
        {"(0 10)(0 x)",                                              {},        {{0, 10}, {0}}                                               },
        {"(0 10)(+ 1 2)",                                            {},        {{0, 10}, {0}}                                               },
        {"(0 10)((+ 1 2))",                                          {},        {{0, 10}, {0}}                                               },
        {"(0 10)(1 2 (1))",                                          {},        {{0, 10}, {0}}                                               },
    };

    Test_data<Dummy, Unified_output, Euler> unified_data = {
        // {  {},                                                       {},           {true, {}}                   },
        {  {{ {{"+ 1 2"}} }, { {{"x"}} }},                                                       {},           {true, {"x"}},                   },
        {  {{ {{"+ 1 x"}} }, { {{"x"}} }},                                                       {},           {true, {"x"}},                   },
        // {  {{ {{"+ 1 x"}, {"- x 5"}} }, { {{"x"}} }},                                            {},           true,                         },
    };

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

    string context_msg = "building of context-s";
    test<Dummy, Context, string>(context_data, context_res, context_msg);
    test<Dummy, Context, string>(context_throw_data, context_res, context_msg, true);

    string unified_msg = "building of solvers";
    test<Dummy, Unified_output, Euler>(unified_data, unified_res, unified_msg);

    // try {
    //     cout << Euler({{{"+ 1 2"}}}, {{{"x"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 x"}}}, {{{"x"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 2"}, {"- x 5"}}}, {{{"x"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 2"}, {"- x 5"}}}, {{{"x"}, {"y"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 2"}, {"- x 5"}}, {{"- 1"}}}, {{{"x"}}, {{"y"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 2"}, {"- x 5"}}, {{"- 1"}}}, {{{"x"}, {"y"}}}) << endl << endl;
    //     cout << Euler({{{"+ 1 2"}, {"- x 5"}}, {{"- 1"}}}, {{{"x"}, {"y"}}, {{"x"}, {"y"}}}) << endl << endl;
    // }
    // catch (const Error& e) {
    //     cerr << e << endl;
    //     throw;
    // }

    cout << endl << "Success." << endl;
    return 0;
}
