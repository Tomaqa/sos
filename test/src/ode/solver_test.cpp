#include "test.hpp"
#include "ode/solver.hpp"
#include "ode/euler.hpp"
#include "ode/odeint.hpp"

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

        using Context = Solver::Context;
        using Ode_spec = Solver::Ode_spec;
        using Solve_ode_output = vector<Real>;
        using Solve_ode_input = tuple<Ode_spec, Param_keys, Context>;
        using Solve_ode_params = tuple<Time>;

        template <typename Solver>
        Solve_ode_output solve_ode_res(const Solve_ode_input& input,
                                       bool should_throw,
                                       Solve_ode_params& params)
        {
            const Ode_spec& ospec = get<0>(input);
            const Param_keys& keys = get<1>(input);
            const Context& ctx = get<2>(input);
            int dt_size_ = ospec.size();
            Solver solver(ospec, keys);
            Time step_size = get<0>(params);
            if (step_size > 0) solver.set_step_size(step_size);
            Solve_ode_output res1;
            Solve_ode_output res2;
            for (int i = 0; i < dt_size_; i++) {
                res1.push_back(solver.solve_ode(i, ctx));
                res2.push_back(solver.solve_ode(i, ctx));
            }
            if (!should_throw) {
                expect(res1 == res2,
                       "Two consecutive solutions differ: '"s\
                       + to_string(res1) + "' != '" + to_string(res2) + "'");

                cout << ospec
                     << "[ " << keys << "]"
                     << " (" << ctx << ")"
                     << " {" << params << "}"
                     << endl << "  -> " << "( " << res1 << ")"
                     << endl;
            }
            return move(res1);
        }

        /////////////////////////////////////////////////////////////////

        using Solve_unif_odes_output = vector<State>;
        using Solve_unif_odes_input = tuple<Odes_spec, Param_keys, Context>;
        using Solve_unif_odes_params = tuple<Time>;
        using Dt_ids = Solver::Dt_ids;

        template <typename Solver>
        Solve_unif_odes_output
            solve_unif_odes_res(const Solve_unif_odes_input& input,
                                bool should_throw,
                                Solve_unif_odes_params& params)
        {
            const Odes_spec& osspec = get<0>(input);
            const Param_keys& keys = get<1>(input);
            const Context& ctx = get<2>(input);
            expect(all_equal(osspec, [](auto& ospec0, auto& ospec){
                                         return ospec0.size() == ospec.size();
                                     }),
                   "Please provide all ODEs with equal size of dt variants "s
                   + "within this test.");
            int size_ = osspec.size();
            int dt_size_ = osspec.front().size();
            Dt_ids dt_ids_(size_);
            Solver solver(osspec, keys);
            Time step_size = get<0>(params);
            if (step_size > 0) solver.set_step_size(step_size);
            Solve_unif_odes_output res1;
            Solve_unif_odes_output res2;
            for (int i = 0; i < dt_size_; i++) {
                std::fill_n(std::begin(dt_ids_), size_, i);
                res1.push_back(solver.solve_unif_odes(dt_ids_, ctx));
                res2.push_back(solver.solve_unif_odes(dt_ids_, ctx));
            }
            if (!should_throw) {
                expect(res1 == res2,
                       "Two consecutive solutions differ: '"s\
                       + to_string(res1) + "' != '" + to_string(res2) + "'");

                cout << osspec
                     << "[ " << keys << "]"
                     << " (" << ctx << ")"
                     << " {" << params << "}"
                     << endl << "  -> " << "( " << res1 << ")"
                     << endl;
            }
            return move(res1);
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

    Test_data<Solve_ode_params, Solve_ode_output, Solve_ode_input> solve_ode_euler_data = {
        {  { { {"- 1"} }, {"x"}, {{0, 0}, {100}} },                                                                                             {-1},       {100}                           },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {-1},       {90}                            },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {1},        {90}                            },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {1},        {2.9525e6}                      },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.1},      {4.1409e9}                      },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.01},     {1.991323e10}                   },
        {  { { {"+ x ( - 10 y)"}, {"+ x y"} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                                                {0.05},     {-7.73159e21, 3.8658e22}        },
        {  { { {"- (/ x 2) (/ t 3)"}, {"- (/ t 3) x"} }, {"x", "t"}, {{0, 50}, {10}} },                                                         {0.02},     {5.5117124e11, 16.3333}         },
    };

    Test_data<Solve_ode_params, Solve_ode_output, Solve_ode_input> solve_ode_odeint_data = {
        {  { { {"- 1"} }, {"x"}, {{0, 0}, {100}} },                                                                                             {-1},       {100}                           },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {-1},       {90}                            },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {1},        {90}                            },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {1},        {2.42585e10}                    },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.1},      {2.425e10}                      },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.01},     {2.42583e10}                    },
        {  { { {"+ x ( - 10 y)"}, {"+ x y"} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                                                {0.05},     {-2.59242e22, 1.29621e23}       },
        {  { { {"- (/ x 2) (/ t 3)"}, {"- (/ t 3) x"} }, {"x", "t"}, {{0, 50}, {10}} },                                                         {0.02},     {6.24e11, 16.3267}              },
    };

    Test_data<Solve_unif_odes_params, Solve_unif_odes_output, Solve_unif_odes_input> solve_unif_odes_euler_data = {
        {  { { {{"- 1"}}, {{"- 1"}} }, {"x", "y"}, {{0, 10}, {100, 50}} },                                                                      {-1},       {{90, 40}}                      },
        {  { { {{"+ x ( - 10 y)"}}, {{"+ 0"}} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                                              {0.05},     {{-7.73159e21, 20}}             },
        {  { { {{"- (/ tt 3) x"}}, {{"+ 1"}} }, {"x", "tt"}, {{0, 50}, {10, 0}} },                                                              {0.02},     {{16.3333, 50}}                 },
    };

    /////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////

    string context_msg = "building of context-s";
    test<Dummy, Context, string>(context_data, context_res, context_msg);
    test<Dummy, Context, string>(context_throw_data, context_res, context_msg, true);

    string keys_msg = "building of solvers";
    test<Keys_params, Keys_output, Keys_input>(keys_data, keys_res, keys_msg);
    test<Keys_params, Keys_output, Keys_input>(keys_throw_data, keys_res, keys_msg, true);

    string solve_ode_msg = "solving single ODE";
    test<Solve_ode_params, Solve_ode_output, Solve_ode_input>(solve_ode_euler_data, solve_ode_res<Euler>,
                                                              solve_ode_msg + " by 'Euler'",
                                                              false, apx_equal<Solve_ode_output>);
    test<Solve_ode_params, Solve_ode_output, Solve_ode_input>(solve_ode_odeint_data, solve_ode_res<Odeint>,
                                                              solve_ode_msg + " by 'Odeint'",
                                                              false, apx_equal<Solve_ode_output>);

    string solve_unif_odes_msg = "solving unified ODEs";
    test<Solve_unif_odes_params, Solve_unif_odes_output, Solve_unif_odes_input>(solve_unif_odes_euler_data, solve_unif_odes_res<Euler>,
                                                              solve_unif_odes_msg + " by 'Euler'",
                                                              false, apx_equal<Solve_unif_odes_output>);

    /////////////////////////////////////////////////////////////////

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
