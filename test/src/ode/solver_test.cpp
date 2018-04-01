#include "test.hpp"
#include "ode/solver.hpp"

using namespace Test;
using namespace ODE;

using Context = Solver::Context;

/////////////////////////////////////////////////////////////////

Context context_res(const string& input, Dummy&)
{
    return Context(input);
}

/////////////////////////////////////////////////////////////////



/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

int main(int, const char*[])
{
    TestData<Dummy, Context> context_data = {
        // {"(0 (0 10) (0))",                                {},                {0, {0, 10}, {0}}                                               },
        // {" (0 (0 10) (0)) ",                              {},                {0, {0, 10}, {0}}                                               },
        // {" (0(0 10) (0) ) ",                              {},                {0, {0, 10}, {0}}                                               },
        // {"0 (0 10) (0)",                                  {},                {0, {0, 10}, {0}}                                               },
        // {" 0  ( -5.0 10.5 )  ( 0 1.1 2 )  ",              {},                {0, {-5, 10.5}, {0, 1.1, 2}}                                    },
        // {" 0  (5.0 10.5 )( 0 1.1 2)  ",                   {},                {0, {5, 10.5}, {0, 1.1, 2}}                                     },
        // {" 0( 5.0 10.5)  (0 1.1 2 )  ",                   {},                {0, {5, 10.5}, {0, 1.1, 2}}                                     },
        // {" 0(0 1)()",                                     {},                {0, {0, 1}, {}}                                                 },
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

/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////

    test<Dummy, Context, string>(context_data, context_res, "building of context-s");

    cout << endl << "Success." << endl;
    return 0;
}
