#include "solver/run.hpp"
#include "ode/euler.hpp"

#ifdef PROFILE
#include <omp.h>

double wall_time;
double check_sat_time = 0;
double other_smt_time = 0;
double ode_time = 0;
#endif //< PROFILE

using namespace SOS;

int main(int argc, const char* argv[])
{
    return Solver<ODE::Euler>::Run(argc, argv).run();
}
