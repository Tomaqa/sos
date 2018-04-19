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

        using Odes_spec = ODE::Odes_spec;
        using Param_keys = ODE::Param_keys;
        using Param_keyss = ODE::Param_keyss;
        using Keys_input = pair<Odes_spec, Param_keyss>;
        using Keys_output = tuple<size_t, bool, bool, Param_keys, Param_keyss>;
        using Keys_params = tuple<bool, bool>;

        template <typename KeysInput>
        Keys_output keys_res(const KeysInput& input, bool should_throw,
                             Keys_params& params)
        {
            bool& quiet = get<0>(params);
            bool unify = get<1>(params);
            Euler solver(input, unify);
            Param_keys param_keys_;
            size_t size = solver.size();
            bool unified = solver.is_unified();
            bool has_unif_t = solver.has_unif_param_t();
            if (unified) param_keys_ = solver.cunif_param_keys();
            Param_keyss param_keyss_ = solver.cparam_keyss();
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
        using Ode_spec = ODE::Ode_spec;
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
            return res1;
        }

        /////////////////////////////////////////////////////////////////

        using Solve_unif_odes_output = vector<State>;
        using Solve_unif_odes_input = tuple<Odes_spec, Param_keys, Context>;
        using Solve_unif_odes_params = tuple<Time>;
        using Dt_ids = ODE::Dt_ids;

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
                       "Two consecutive solutions differ: '"s
                       + to_string(res1) + "' != '" + to_string(res2) + "'");

                cout << osspec
                     << "[ " << keys << "]"
                     << " (" << ctx << ")"
                     << " {" << params << "}"
                     << endl << "  -> " << "( " << res1 << ")"
                     << endl;
            }
            return res1;
        }

        /////////////////////////////////////////////////////////////////

        using Contexts = Solver::Contexts;
        using Solve_odes_output = vector<State>;
        using Solve_odes_input = tuple<Odes_spec, Param_keyss, Contexts>;
        using Solve_odes_params = tuple<Time>;

        template <typename Solver>
        Solve_odes_output
            solve_odes_res(const Solve_odes_input& input,
                           bool should_throw,
                           Solve_odes_params& params)
        {
            const Odes_spec& osspec = get<0>(input);
            const Param_keyss& keyss = get<1>(input);
            const Contexts& ctxs = get<2>(input);
            expect(all_equal(osspec, [](auto& ospec0, auto& ospec){
                                         return ospec0.size() == ospec.size();
                                     }),
                   "Please provide all ODEs with equal size of dt variants "s
                   + "within this test.");
            int size_ = osspec.size();
            int dt_size_ = osspec.front().size();
            Dt_ids dt_ids_(size_);
            Solver solver(osspec, keyss);
            Time step_size = get<0>(params);
            if (step_size > 0) solver.set_step_size(step_size);
            Solve_odes_output res1;
            Solve_odes_output res2;
            for (int i = 0; i < dt_size_; i++) {
                std::fill_n(std::begin(dt_ids_), size_, i);
                res1.push_back(solver.solve_odes(dt_ids_, ctxs));
                res2.push_back(solver.solve_odes(dt_ids_, ctxs));
            }
            if (!should_throw) {
                expect(res1 == res2,
                       "Two consecutive solutions differ: '"s
                       + to_string(res1) + "' != '" + to_string(res2) + "'");

                cout << osspec
                     << "[ " << keyss << "]"
                     << " (" << ctxs << ")"
                     << " {" << params << "}"
                     << endl << "  -> " << "( " << res1 << ")"
                     << endl;
            }
            return res1;
        }

        /////////////////////////////////////////////////////////////////

        template <typename Solver>
        State solve_res(const string& input,
                        bool should_throw,
                        Dummy&)
        {
            string spec1;
            string spec2;
            istringstream iss1(input);
            istringstream iss2(input);
            getline(iss1, spec1);
            getline(iss2, spec2);
            Solver solver1(spec1);
            Solver solver2(spec2);
            State res1 = solver1.solve(iss1);
            State res2 = solver2.solve(iss2);
            if (!should_throw) {
                expect(res1 == res2,
                       "Two consecutive solutions differ: '"s
                       + to_string(res1) + "' != '" + to_string(res2) + "'");

                cout << Expr(input)
                     << endl << "  -> " << "( " << res1 << ")"
                     << endl;
            }
            return res1;
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
        {  {},                                                                                 {true, false},            {0, false, false, {}, {} }                                                },
        {  {{}, {}},                                                                           {true, false},            {0, false, false, {}, {} }                                                },
        {  {{ {{"+ 1 2"}} }, { {"x"} }},                                                       {false, false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 2"}} }, { {"x", "y"} }},                                                  {false, false},           {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  {{ {{"+ 1 x"}} }, { {"x"} }},                                                       {false, false},           {1, true, false, {"x"}, {{"x"}} },                                        },
        {  {{ {{"+ 1 x"}, {"- x 5"}} }, { {"x", "y"} }},                                       {false, false},           {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"} }},                            {false, false},           {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x"}, {"y"} }},                          {false, false},           {2, false, false, {}, {{"x"}, {"y"}} },                                   },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x"}, {"y"} }},                          {false, true},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"x", "y"} }},                {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"y", "x"} }},                {false, false},           {2, false, false, {}, {{"x", "y"}, {"y", "x"}} },                         },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- 1"}} }, { {"x", "y"}, {"y", "x"} }},                {false, true},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y", "t"} }},            {false, false},           {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "y"} }},                 {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x"}, {"y"} }},               {false, false},           {2, false, false, {}, {{"x"}, {"y", "t"}} },                              },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x"}, {"y"} }},               {false, true},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
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
        {  {{ {{}} }, { {"x"} }},                                                              {},                {}                                                                        },
        {  {{ {{"- 1"}} }, { {""} }},                                                          {},                {}                                                                        },
        {  {{ {{"- 1"}} }, { {"t"} }},                                                         {},                {}                                                                        },
        {  {{ {{"+ 1 x"}, {"- x 5"}}, {{"- t"}, {"* y 2"}} }, { {"x", "t", "y"} }},            {},                {},                                                                       },
    };

    Test_data<Keys_params, Keys_output> keys_string_data = {
        {  "() ()",                                                                            {true, false},            {0, false, false, {}, {} }                                                },
        {  "( ((+ 1 2)) ) ( (x) )",                                                            {true, false},            {1, true, false, {"x"}, {{"x"}} },                                        },
        {  "( ((+ 1 2)) ) (  x  )",                                                            {true, false},            {1, true, false, {"x"}, {{"x"}} },                                        },
        {  "( (( + 1 2 )) )  (   (x    y)   )",                                                {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) )  (    x    y    )",                                                {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) )  (   (x    y)   )",                                                {true, true},             {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) )  (    x    y    )",                                                {true, true},             {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) ) * (   (x    y)   )",                                               {true, true},             {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) ) * (    x    y    )",                                               {true, true},             {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) ) * (   (x    y)   )",                                               {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( (( + 1 2 )) ) * (    x    y    )",                                               {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( ((+ 1 x)) ) ( x )",                                                              {true, false},            {1, true, false, {"x"}, {{"x"}} },                                        },
        {  "( ((+ 1 x) (- x 5)) ) ( (x y) )",                                                  {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( ((+ 1 x) (- x 5)) ) (  x y  )",                                                  {true, false},            {1, true, false, {"x", "y"}, {{"x", "y"}} },                              },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) ( (x y) )",                                          {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) (  x y  )",                                          {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) ( (x) (y) )",                                        {true, false},            {2, false, false, {}, {{"x"}, {"y"}} },                                   },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) ( (x y) (x y) )",                                    {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) * ( (x y) (x y) )",                                  {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) ( (x y) (y x) )",                                    {true, false},            {2, false, false, {}, {{"x", "y"}, {"y", "x"}} },                         },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) * ( (x y) (y x) )",                                  {true, false},            {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- 1)) ) ( (x y) (y x) )",                                    {true, true},             {2, true, false, {"x", "y"}, {{"x", "y"}, {"x", "y"}} },                  },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) ( (x y t) )",                                {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) (  x y t  )",                                {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) ( (x y) )",                                  {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) (  x y  )",                                  {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) ( (x) (y) )",                                {true, false},            {2, false, false, {}, {{"x"}, {"y", "t"}} },                              },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) * ( (x) (y) )",                              {true, false},            {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) ( (x) (y) )",                                {true, true},             {2, true, true, {"x", "y", "t"}, {{"x", "y", "t"}, {"x", "y", "t"}} },    },
    };

    Test_data<Keys_params, Keys_output> keys_throw_string_data = {
        {  "() ( () )",                                                                       {},                {}                                                                        },
        {  "() ( (x) )",                                                                      {},                {}                                                                        },
        {  "( () ) ()",                                                                       {},                {}                                                                        },
        {  "( () ) ( () )",                                                                   {},                {}                                                                        },
        {  "( () ) ( (x) )",                                                                  {},                {}                                                                        },
        {  "( ((- 1)) ) ()",                                                                  {},                {}                                                                        },
        {  "( ((- 1)) ) ( () )",                                                              {},                {}                                                                        },
        {  "( ((- 1)) ) ( (x) (y) )",                                                         {},                {}                                                                        },
        {  "( ((- 1)) ((+ 2)) ) ( (x) (y) (z) )",                                             {},                {}                                                                        },
        {  "( ((- 1)) ((+ 2)) ((* 1)) ) ( (x) (y) )",                                         {},                {}                                                                        },
        {  "( ((-)) ) ( (x) )",                                                               {},                {}                                                                        },
        {  "( (()) ) ( (x) )",                                                                {},                {}                                                                        },
        {  "( ((- 1)) ) ( () )",                                                              {},                {}                                                                        },
        {  "( ((- 1)) ) ( (t) )",                                                             {},                {}                                                                        },
        {  "( ((+ 1 x) (- x 5)) ((- t) (* y 2)) ) ( (x t y) )",                               {},                {},                                                                       },
    };

    Test_data<Solve_ode_params, Solve_ode_output, Solve_ode_input> solve_ode_euler_data = {
        {  { { {"- 1"} }, {"x"}, {{0, 0}, {100}} },                                                                                             {-1},       {100}                           },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {-1},       {90}                            },
        {  { { {"- 1"} }, {"x"}, {{0, 10}, {100}} },                                                                                            {1},        {90}                            },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {1},        {2.9525e6}                      },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.1},      {4.1409e9}                      },
        {  { { {"- (* 2 x) 100"} }, {"x"}, {{0, 10}, {100}} },                                                                                  {0.01},     {1.991323e10}                   },
        {  { { {"+ x ( - 10 y)"}, {"+ x y"} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                                                {0.05},     {-7.73159e21, 3.8658e22}        },
        {  { { {"- (/ x 2) (/ t 3)"}, {"- (/ t 3) x"} }, {"x", "t"}, {{0, 50}, {10}} },                                                         {0.02},     {5.5e11, 16.34}                 },
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
        {  { { {{"- 1"}}, {{"- 1"}} }, {"x", "y"}, {{0, 10}, {100, 50}} },                                                                      {-1},       {{90, 40}}                                        },
        {  { { {{"+ x ( - 10 y)"}, {"+ x y"}}, {{"+ 0"}, {"+ 0"}} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                          {0.05},     {{-7.73159e21, 20}, {3.8658e22, 20}}              },
        {  { { {{"- (/ tt 3) x"}, {"- (/ x 2) (/ tt 3)"}}, {{"+ 1"}, {"+ 1"}} }, {"x", "tt"}, {{0, 50}, {10, 0}} },                             {0.02},     {{16.3333, 50}, {5.5e11, 50}}                     },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt"}, {{0, 10}, {100, 0}} },                                                                   {-1},       {{100, 10}}                                       },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt", "t"}, {{0, 10}, {100, 0}} },                                                              {-1},       {{100, 10}}                                       },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt", "y", "t"}, {{0, 10}, {100, 0, 999}} },                                                    {-1},       {{100, 10}}                                       },
    };
    Test_data<Solve_unif_odes_params, Solve_unif_odes_output, Solve_unif_odes_input> solve_unif_odes_odeint_data = {
        {  { { {{"- 1"}}, {{"- 1"}} }, {"x", "y"}, {{0, 10}, {100, 50}} },                                                                      {-1},       {{90, 40}}                                        },
        {  { { {{"+ x ( - 10 y)"}, {"+ x y"}}, {{"+ 0"}, {"+ 0"}} }, {"x", "y"}, {{0, 50}, {5, 20}} },                                          {0.05},     {{-2.59242e22, 20}, {1.29621e23, 20}}             },
        {  { { {{"- (/ tt 3) x"}, {"- (/ x 2) (/ tt 3)"}}, {{"+ 1"}, {"+ 1"}} }, {"x", "tt"}, {{0, 50}, {10, 0}} },                             {0.02},     {{16.3267, 50}, {6.24e11, 50}}                    },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt"}, {{0, 10}, {100, 0}} },                                                                   {-1},       {{100, 10}}                                       },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt", "t"}, {{0, 10}, {100, 0}} },                                                              {-1},       {{100, 10}}                                       },
        {  { { {{"- t tt"}}, {{"+ 1"}} }, {"x", "tt", "y", "t"}, {{0, 10}, {100, 0, 999}} },                                                    {-1},       {{100, 10}}                                       },
    };

    Test_data<Solve_odes_params, Solve_odes_output, Solve_odes_input> solve_odes_euler_data = {
        {  { { {{"- 1"}}, {{"+ 1"}} }, {{"x"}, {"y"}}, { {{0, 10}, {100}}, {{50, 70}, {20}} }  },                                               {-1},       {{90, 40}}                                      },
        {  { { {{"+ x ( - 10 y)"}, {"+ x y"}}, {{"+ 1"}, {"- 1"}} }, {{"x", "y"}, {"y", "x"}}, {{{0, 50}, {5, 20}}, {{0, 50}, {5, 20}}} },      {0.05},     {{-7.73159e21, 55}, {3.8658e22, -45}}           },
        {  { { {{"+ x ( - 10 20)"}, {"+ x 20"}}, {{"+ 1"}, {"- 1"}} }, {{"x", "y"}, {"x", "y"}}, {{{0, 50}, {5, 20}}, {{0, 50}, {5, 20}}} },    {0.05},     {{-7.73159e21, 70}, {3.8658e22, -30}}           },
        {  { { {{"- (/ t 3) x"}, {"- (/ x 2) (/ t 3)"}}, {{"+ 1"}, {"+ 1"}} }, {{"x"}, {"tt", "x"}}, {{{0, 50}, {10}}, {{0, 50}, {0, 30}}} },   {0.02},     {{16.34, 50}, {5.5e11, 50}}                     },
        {  { { {{"- (/ t 3) x"}, {"- (/ x 2) (/ tt 3)"}}, {{"+ 1"}, {"+ 1"}} }, {{"x", "tt"}, {"tt", "x"}}, {{{0, 50}, {10, 0}}, {{0, 50}, {0, 30}}} },  {0.02},     {{16.34, 50}, {6.35967e11, 50}}        },
        {  { { {{"- (* 2 x) 100"}}, {{"+ y ( - 10 z)"}} }, {{"x"}, {"y", "z"}}, {{{0, 10}, {100}}, {{0, 50}, {5, 20}}} },                       {0.05},     {{9.49526e9, -7.73159e21}}                      },
        {  { { {{"- (* 2 x) 100"}}, {{"+ y ( - 10 z)"}} }, {{"x", "z"}, {"y", "z", "x"}}, {{{0, 10}, {100, 20}}, {{0, 50}, {5, 20, 100}}} },    {0.05},     {{9.49526e9, -7.73159e21}}                      },
    };
    Test_data<Solve_odes_params, Solve_odes_output, Solve_odes_input> solve_odes_odeint_data = {
        {  { { {{"- 1"}}, {{"+ 1"}} }, {{"x"}, {"y"}}, { {{0, 10}, {100}}, {{50, 70}, {20}} }  },                                               {-1},       {{90, 40}}                                      },
        {  { { {{"+ x ( - 10 y)"}, {"+ x y"}}, {{"+ 1"}, {"- 1"}} }, {{"x", "y"}, {"y", "x"}}, {{{0, 50}, {5, 20}}, {{0, 50}, {5, 20}}} },      {0.05},     {{-2.59242e22, 55}, {1.29621e23, -45}}          },
        {  { { {{"+ x ( - 10 20)"}, {"+ x 20"}}, {{"+ 1"}, {"- 1"}} }, {{"x", "y"}, {"x", "y"}}, {{{0, 50}, {5, 20}}, {{0, 50}, {5, 20}}} },    {0.05},     {{-2.59242e22, 70}, {1.29621e23, -30}}          },
        {  { { {{"- (/ t 3) x"}, {"- (/ x 2) (/ t 3)"}}, {{"+ 1"}, {"+ 1"}} }, {{"x"}, {"tt", "x"}}, {{{0, 50}, {10}}, {{0, 50}, {0, 30}}} },   {0.02},     {{16.3267, 50}, {6.24e11, 50}}                  },
        {  { { {{"- (/ t 3) x"}, {"- (/ x 2) (/ tt 3)"}}, {{"+ 1"}, {"+ 1"}} }, {{"x", "tt"}, {"tt", "x"}}, {{{0, 50}, {10, 0}}, {{0, 50}, {0, 30}}} },  {0.02},     {{16.3267, 50}, {7.2e11, 50}}          },
        {  { { {{"- (* 2 x) 100"}}, {{"+ y ( - 10 z)"}} }, {{"x"}, {"y", "z"}}, {{{0, 10}, {100}}, {{0, 50}, {5, 20}}} },                       {0.05},     {{2.425e10, -2.59242e22}}                       },
        {  { { {{"- (* 2 x) 100"}}, {{"+ y ( - 10 z)"}} }, {{"x", "z"}, {"y", "z", "x"}}, {{{0, 10}, {100, 20}}, {{0, 50}, {5, 20, 100}}} },    {0.05},     {{2.425e10, -2.59242e22}}                       },
    };

    Test_data<Dummy, State, string> solve_euler_data = {
        {  "( ((- 1)) ) (x) \n (0) ( ((0 10) (100)) )",                                                                                          {},       {90}                           },
        {  "( ((- 1)) ) ((x)) \n (0) ( ((0 10) (100)) )",                                                                                        {},       {90}                           },
        {  "( ((- y)) ((+ 1)) ) ((x y)(y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                          {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y)(x y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                    {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                           {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                         {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)(x y)) \n (0 0) ( ((0 10) (100 0)) )",                                                                     {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y) \n (0 0) ( ((0 10) (100 0)) )",                                                                            {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)) \n (0 0) ( ((0 10) (100 0)) )",                                                                          {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y t) \n (0 0) ( ((0 10) (100 0)) )",                                                                          {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y t)(y t)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                      {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y)(y t)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                        {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y t)(y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                        {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y z t)(y z)) \n (0 0) ( ((0 10) (100 0 999)) ((0 10) (0 999)) )",                                            {},       {100, 10}                      },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )(  p gam om r t  ) \n (0 0) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-5.0, 1.0}                    },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) ) \n (0 0) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-5.0, 1.0}                    },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) (gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ) ( (0.0 1.0) (1.0 2.0 5.0) ))", {}, {-5.0, 3.0}   },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-9.95, 3.0}                 },
    };
    Test_data<Dummy, State, string> solve_euler_throw_data = {
        {  "( (- 1) ) (x) \n (0) ( ((0 10) (100)) )",                                                                                            {},       {}                            },
        {  "( - 1 ) (x) \n (0) ( ((0 10) (100)) )",                                                                                              {},       {}                            },
        {  "( ((- 1)) ) (x) \n ( ((0 10) (100)) )",                                                                                              {},       {}                            },
        {  "( ((- y)) ((+ 1)) ) (x y) \n (0 0) ( (0 10) (100 0) )",                                                                              {},       {}                            },
        {  "( ((- 1)) ) ! (x) \n (0) ( ((0 10) (100)) )",                                                                                        {},       {}                            },
        {  "( ((- 1)) ) () (x) \n (0) ( ((0 10) (100)) )",                                                                                       {},       {}                            },
        {  "( ((- 1)) ) (*) (x) \n (0) ( ((0 10) (100)) )",                                                                                      {},       {}                            },
    };

    Test_data<Dummy, State, string> solve_odeint_data = {
        {  "( ((- 1)) ) (x) \n (0) ( ((0 10) (100)) )",                                                                                          {},       {90}                           },
        {  "( ((- 1)) ) ((x)) \n (0) ( ((0 10) (100)) )",                                                                                        {},       {90}                           },
        {  "( ((- y)) ((+ 1)) ) ((x y)(y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                          {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y)(x y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                    {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                           {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (100 0)) )",                                                         {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)(x y)) \n (0 0) ( ((0 10) (100 0)) )",                                                                     {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y) \n (0 0) ( ((0 10) (100 0)) )",                                                                            {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y)) \n (0 0) ( ((0 10) (100 0)) )",                                                                          {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) (x y t) \n (0 0) ( ((0 10) (100 0)) )",                                                                          {},       {50, 10}                       },
        {  "( ((- y)) ((+ 1)) ) ((x y t)(y t)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                      {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y)(y t)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                        {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y t)(y)) \n (0 0) ( ((0 10) (100 0)) ((0 10) (0)) )",                                                        {},       {100, 10}                      },
        {  "( ((- y)) ((+ 1)) ) ((x y z t)(y z)) \n (0 0) ( ((0 10) (100 0 999)) ((0 10) (0 999)) )",                                            {},       {100, 10}                      },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )(  p gam om r t  ) \n (0 0) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-5.0, 1.0}                    },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) ) \n (0 0) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-5.0, 1.0}                    },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) (gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ) ( (0.0 1.0) (1.0 2.0 5.0) ))", {}, {-5.0, 3.0}   },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) )( (p gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",                   {},       {-10, 3.0}                     },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) ) * ( (p gam om r t) (gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 2.0 5.0) ))",   {},       {-10.0, 3.0}                   },
        {  "( (( * ( - r ) gam )) (( + 0 ) ( - om ) ( + om )) ) * ( (p gam r om t) (gam om r t) ) \n (0 2) (( (0.0 1.0) (0.0 1.0 5.0 2.0) ))",   {},       {-10.0, 3.0}                   },
    };

    /////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////

    string context_msg = "building of context-s";
    test<Dummy, Context, string>(context_data, context_res, context_msg);
    test<Dummy, Context, string>(context_throw_data, context_res, context_msg, true);

    string keys_msg = "building of solvers";
    test<Keys_params, Keys_output, Keys_input>(keys_data, keys_res<Keys_input>, keys_msg);
    test<Keys_params, Keys_output, Keys_input>(keys_throw_data, keys_res<Keys_input>, keys_msg, true);

    string keys_string_msg = keys_msg + " from string";
    test<Keys_params, Keys_output, string>(keys_string_data, keys_res<string>, keys_string_msg);
    test<Keys_params, Keys_output, string>(keys_throw_string_data, keys_res<string>, keys_string_msg, true);

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
    test<Solve_unif_odes_params, Solve_unif_odes_output, Solve_unif_odes_input>(solve_unif_odes_odeint_data, solve_unif_odes_res<Odeint>,
                                                              solve_unif_odes_msg + " by 'Odeint'",
                                                              false, apx_equal<Solve_unif_odes_output>);

    string solve_odes_msg = "solving non-unified ODEs";
    test<Solve_odes_params, Solve_odes_output, Solve_odes_input>(solve_odes_euler_data, solve_odes_res<Euler>,
                                                              solve_odes_msg + " by 'Euler'",
                                                              false, apx_equal<Solve_odes_output>);
    test<Solve_odes_params, Solve_odes_output, Solve_odes_input>(solve_odes_odeint_data, solve_odes_res<Odeint>,
                                                              solve_odes_msg + " by 'Odeint'",
                                                              false, apx_equal<Solve_odes_output>);

    string solve_msg = "solving ODE(s) specified in strings";
    test<Dummy, State, string>(solve_euler_data, solve_res<Euler>, solve_msg + " by 'Euler'",
                               false, apx_equal<State>);
    test<Dummy, State, string>(solve_euler_throw_data, solve_res<Euler>, solve_msg + " by 'Euler'",
                               true, apx_equal<State>);
    test<Dummy, State, string>(solve_odeint_data, solve_res<Odeint>, solve_msg + " by 'Odeint'",
                               false, apx_equal<State>);

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

    //! 414 735 allocs

    cout << endl << "Success." << endl;
    return 0;
}
catch (const SOS::Error& e) {
    std::cout << e << std::endl;
    throw;
}
