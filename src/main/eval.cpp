#include "expr/eval/run.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return Expr::Eval<double>::Run(argc, argv).run();
}
