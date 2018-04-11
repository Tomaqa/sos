#include <iostream>
#include <iomanip>

namespace SOS {
    using std::cin;
    using std::cout;
    using std::cerr;
    using std::endl;

    template <typename Arg>
    int Expr::Eval<Arg>::Run::run(int argc, const char* argv[])
    try {
        Stream_ptr<istream> is_ptr(run_get_istream(argc, argv));

        string line;
        while (getline(*is_ptr, line)) {
            _expr = Expr(line);
            if (_expr.empty()) continue;
            if (_expr.size() == 1) {
                // cout << _expr.cto_token(0) << endl;
                cout << _expr.cto_etoken(0) << endl;
                continue;
            }

            cout << std::setprecision(8);
            _eval = _expr.get_eval<Arg>();
            if (_eval.size() == 0) {
                cout << _eval() << endl;
                continue;
            }

            while (getline(*is_ptr, line)) {
                if (line.empty()) continue;
                Expr e_values(line);
                Param_values values(e_values.transform_to_args<Arg>());
                cout << _eval(move(values)) << endl;
                break;
            }
        }

        return 0;
    }
    catch (const Error& err) {
        cerr << err << endl;
        return 1;
    }
}
