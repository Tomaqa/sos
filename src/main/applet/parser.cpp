#include "parser/run.hpp"

using namespace SOS;

int main(int argc, const char* argv[])
{
    return Parser::Run(argc, argv).run();
}
