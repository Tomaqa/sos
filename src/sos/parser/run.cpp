#include "parser/run.hpp"

#include <iostream>

namespace SOS {
    using std::cin;
    using std::cout;
    using std::cerr;
    using std::endl;

    int Parser::Run::run(int argc, const char* argv[])
    try {
        Stream_ptr<istream> is_ptr(run_get_istream(argc, argv));

        _parser = Parser(*is_ptr);

        cout << _parser.smt_input() << endl;

        return 0;
    }
    catch (const Error& err) {
        cerr << err << endl;
        return 1;
    }
}
