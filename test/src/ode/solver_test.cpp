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
        using Param_keyss = Solver::Param_keyss;
        using Keys_output = tuple<size_t, bool, bool, Param_keys, Param_keyss>;
        using Keys_params = tuple<bool>;

        Keys_output keys_res(const Euler& solver, bool should_throw,
                             Keys_params& params)
        {
            Param_keys param_keys_;
            size_t size = solver.size();
            bool unified = solver.is_unified();
            bool has_t = solver.has_param_t();
            if (unified) param_keys_ = solver.cunif_param_keys();
            Param_keyss param_keyss_ = solver.cparam_keyss();
            bool& quiet = get<0>(params);
            if (!should_throw && !quiet) {
                quiet = true;
                cout << solver
                     << " >> size: " << size
                     << endl << endl;
            }
            return Keys_output(size, unified, has_t,
                               move(param_keys_), move(param_keyss_));
        }

        /////////////////////////////////////////////////////////////////
    }
}


/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
try {
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

    Test_data<Keys_params, Keys_output, Euler> keys_data = {
        {  {},                                                                                 {false},           {0, false, false, {}, {} }                                                },
        {  {{}, {}},                                                                           {true},            {0, false, false, {}, {} }                                                },
        {  {{ {{"+ 1 2"}} }, { {"x"} }},                                                       {false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 x"}} }, { {"x"} }},                                                       {false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 x"}, {"- x 5"}} }, { {"x", "y"} }},                                       {false},           {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"} }},                            {false},           {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x"}, {"y"} }},                          {false},           {2, false, false, {}, {{"x"}, {"y"}} },                                   },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"x", "y"} }},                {true},           {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"y", "x"} }},                {false},           {2, false, false, {}, {{"x", "y"}, {"y", "x"}} },                         },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y", "t"} }},            {false},           {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y"} }},                 {true},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "t", "y"} }},            {false},           {2, true, false, {"x", "t", "y"}, {{"x", "t", "y"}, {"x", "t", "y"}} },    },
    };

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

    string context_msg = "building of context-s";
    test<Dummy, Context, string>(context_data, context_res, context_msg);
    test<Dummy, Context, string>(context_throw_data, context_res, context_msg, true);

    string keys_msg = "building of solvers";
    test<Keys_params, Keys_output, Euler>(keys_data, keys_res, keys_msg);

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
catch (const SOS::Error& e) {
    std::cout << e << std::endl;
    throw;
}
