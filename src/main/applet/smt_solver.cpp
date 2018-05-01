#include "smt/solver/run.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return SMT::Solver::Run(argc, argv).run();
}
