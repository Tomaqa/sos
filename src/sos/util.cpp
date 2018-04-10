#include "util.hpp"

#include <iostream>
#include <istream>
#include <fstream>

namespace SOS {
    using std::cin;

    Util::Flag::Value Util::Flag::value_of(bool set_)
    {
        return set_ ? Value::set : Value::unset;
    }

    Util::Stream_ptr<istream>
        Util::run_get_istream(int argc, const char* argv[])
    {
        static ifstream ifs;
        istream* is_ptr;
        if (argc == 1) {
            is_ptr = &cin;
        }
        else {
            expect(argc == 2, "Additional arguments, "s
                              + "input file name expected.");
            ifs = ifstream(argv[1]);
            is_ptr = &ifs;
        }
        expect(is_ptr->good(), "Input stream error.");
        return is_ptr;
    }
}
