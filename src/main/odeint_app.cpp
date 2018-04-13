#include "ode/solver/run.hpp"
#include "ode/odeint.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return ODE::Solver::Run<ODE::Odeint>().run(argc, argv);
}
