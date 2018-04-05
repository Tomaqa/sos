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

        using Odes_spec = Solver::Odes_spec;
        using Param_keys = Solver::Param_keys;
        using Param_keyss = Solver::Param_keyss;
        using Keys_input = pair<Odes_spec, Param_keyss>;
        using Keys_output = tuple<size_t, bool, bool, Param_keys, Param_keyss>;
        using Keys_params = tuple<bool>;

        Keys_output keys_res(const Keys_input& input, bool should_throw,
                             Keys_params& params)
        {
            Euler solver(input.first, input.second);
            Param_keys param_keys_;
            size_t size = solver.size();
            bool unified = solver.is_unified();
            bool has_unif_t = solver.has_unif_param_t();
            if (unified) param_keys_ = solver.cunif_param_keys();
            Param_keyss param_keyss_ = solver.cparam_keyss();
            bool& quiet = get<0>(params);
            if (!should_throw && !quiet) {
                quiet = true;
                cout << solver
                     << " >> size: " << size
                     << endl << endl;
            }
            return Keys_output(size, unified, has_unif_t,
                               move(param_keys_), move(param_keyss_));
        }

        /////////////////////////////////////////////////////////////////

        using Solve_ode_output = Real;
        using Context = Solver::Context;
        using Solve_ode_input = tuple<Param_keyss, Context>;

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

    Test_data<Keys_params, Keys_output, Keys_input> keys_data = {
        {  {},                                                                                 {true},            {0, false, false, {}, {} }                                                },
        {  {{}, {}},                                                                           {true},            {0, false, false, {}, {} }                                                },
        {  {{ {{"+ 1 2"}} }, { {"x"} }},                                                       {false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 2"}} }, { {"x", "y"} }},                                                  {false},           {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  {{ {{"+ 1 x"}} }, { {"x"} }},                                                       {false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 x"}, {"- x 5"}} }, { {"x", "y"} }},                                       {false},           {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"} }},                            {false},           {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x"}, {"y"} }},                          {false},           {2, false, false, {}, {{"x"}, {"y"}} },                                   },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"x", "y"} }},                {true},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"y", "x"} }},                {false},           {2, false, false, {}, {{"x", "y"}, {"y", "x"}} },                         },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y", "t"} }},            {false},           {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y"} }},                 {true},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "t", "y"} }},            {false},           {2, true, false, {"x", "t", "y"}, {{"x", "t", "y"}, {"x", "t", "y"}} },   },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x"}, {"y"} }},               {false},           {2, false, false, {}, {{"x"}, {"y", "t"}} },                              },
    };

    Test_data<Keys_params, Keys_output, Keys_input> keys_throw_data = {
        {  {{}, { {} }},                                                                       {},                {}                                                                        },
        {  {{}, { {"x"} }},                                                                    {},                {}                                                                        },
        {  {{ {} }, {}},                                                                       {},                {}                                                                        },
        {  {{ {} }, { {} }},                                                                   {},                {}                                                                        },
        {  {{ {} }, { {"x"} }},                                                                {},                {}                                                                        },
        {  {{ {{"- 1"}} }, {}},                                                                {},                {}                                                                        },
        {  {{ {{"- 1"}} }, { {} }},                                                            {},                {}                                                                        },
        {  {{ {{"- 1"}} }, { {"x"}, {"y"} }},                                                  {},                {}                                                                        },
        {  {{ {{"- 1"}}, {{"+ 2"}} }, { {"x"}, {"y"}, {"z"} }},                                {},                {}                                                                        },
        {  {{ {{"- 1"}}, {{"+ 2"}}, {{"* 1"}} }, { {"x"}, {"y"} }},                            {},                {}                                                                        },
        {  {{ {{"-"}} }, { {"x"} }},                                                           {},                {}                                                                        },
        {  {{ {{""}} }, { {"x"} }},                                                            {},                {}                                                                        },
        {  {{ {{"- 1"}} }, { {""} }},                                                          {},                {}                                                                        },
    };

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

    string context_msg = "building of context-s";
    test<Dummy, Context, string>(context_data, context_res, context_msg);
    test<Dummy, Context, string>(context_throw_data, context_res, context_msg, true);

    string keys_msg = "building of solvers";
    test<Keys_params, Keys_output, Keys_input>(keys_data, keys_res, keys_msg);
    test<Keys_params, Keys_output, Keys_input>(keys_throw_data, keys_res, keys_msg, true);

    Euler s1;
    expect(s1.size() == 0 && !s1.is_unified() && !s1.has_unif_param_t()
           && s1.cparam_keyss().empty(),
           "Default construction of 'Solver' failed.");

    auto& dcase = keys_data[5];
    auto& input = get<0>(dcase);
    auto& output = get<2>(dcase);
    Euler s2(input.first, input.second.front());
    expect(s2.size() == get<0>(output)
           && s2.is_unified() == true
           && s2.has_unif_param_t() == get<2>(output)
           && s2.cunif_param_keys() == get<3>(output),
           "Construction of 'Solver' with single parameter keys failed.");

    Euler s3(input.first.front(), input.second.front());
    expect(s3.size() == get<0>(output)
           && s3.is_unified() == true
           && s3.has_unif_param_t() == get<2>(output)
           && s3.cunif_param_keys() == get<3>(output),
           "Construction of 'Solver' with single parameter keys "s
           + "and single ODE specification failed.");

    Param_keyss keyss{get<3>(output)};
    Param_keys new_keys{"?"};
    Euler s4 = move(s3);
    s4.add_ode_spec({{"+ 1"}}, new_keys);
    keyss.emplace_back(new_keys);
    expect(s4.size() == get<0>(output)+1
           && s4.is_unified() == false
           && s4.has_unif_param_t() == false
           && s4.cparam_keyss() == keyss,
           "Move construction of 'Solver' "s
           + "with adding ODE specification failed"s);

    Euler s5 = s2;
    s5.add_ode_spec({{"+ 1"}}, new_keys);
    expect(s2.size() == get<0>(output) && s5.size() == get<0>(output)+1
           && s2.is_unified() == true && s4.is_unified() == false
           && s2.has_unif_param_t() == get<2>(output) && s4.has_unif_param_t() == false
           && s2.cunif_param_keys() == get<3>(output) && s4.cparam_keyss() == keyss,
           "Copy construction of 'Solver' "s
           + "with adding ODE specification failed"s);

    cout << endl << "Success." << endl;
    return 0;
}
catch (const SOS::Error& e) {
    std::cout << e << std::endl;
    throw;
}
