#include "solver/run.hpp"
#include "ode/odeint.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return Solver<ODE::Odeint>::Run(argc, argv).run();
}
