#pragma once

#include "sos.hpp"
#include "parser.hpp"

namespace SOS {
    class Parser::Run {
    public:
        int run(int argc, const char* argv[]);
    private:
        Parser _parser;
    };
}
