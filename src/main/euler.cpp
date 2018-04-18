#include "ode/solver/run.hpp"
#include "ode/euler.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return ODE::Solver::Run<ODE::Euler>(argc, argv).run();
}
