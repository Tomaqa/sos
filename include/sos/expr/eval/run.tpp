#include <iostream>
#include <fstream>

namespace SOS {
    using std::cin;
    using std::cout;
    using std::cerr;
    using std::endl;
    using std::ifstream;

    template <typename Arg>
    int Expr::Eval<Arg>::Run::run(int argc, const char* argv[])
    try {
        ifstream ifs;
        istream* is_ptr;
        bool stdin = false;
        if (argc == 1) {
            is_ptr = &cin;
            stdin = true;
        }
        else {
            expect(argc == 2, "Additional arguments, "s
                              + "input file name expected.");
            ifs = ifstream(argv[1]);
            is_ptr = &ifs;
        }
        expect(is_ptr->good(), "Input stream error.");

        string line;
        getline(*is_ptr, line);
        _expr = Expr(line);
        _eval = _expr.get_eval<Arg>();

        if (_eval.size() == 0) {
            cout << _eval() << endl;
            return 0;
        }

        while (getline(*is_ptr, line)) {
            if (line.empty()) continue;
            Expr e_values(line);
            Param_values values(e_values.transform_to_args<Arg>());
            cout << _eval(move(values)) << endl;
        }

        return 0;
    }
    catch (const Error& err) {
        cerr << err << endl;
        return 1;
    }
}
