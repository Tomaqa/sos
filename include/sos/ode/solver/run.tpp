#include <iostream>
#include <iomanip>

namespace SOS {
    using std::cin;
    using std::cout;
    using std::cerr;
    using std::endl;

    namespace ODE {
        template <typename S>
        typename Solver::Run<S>::Solver_ptr
            Solver::Run<S>::new_solver(S&& solver_)
        {
            return make_unique<S>(forward<S>(solver_));
        }

        template <typename S>
        int Solver::Run<S>::run(int argc, const char* argv[])
        try {
            Stream_ptr<istream> is_ptr(run_get_istream(argc, argv));

            string line;
            getline(*is_ptr, line);
            _solver_ptr = new_solver(S(move(to_string(line))));
            Expr keys_expr;
            if (_solver_ptr->is_unified()) {
                const Param_keys& pkeys = _solver_ptr->cunif_param_keys();
                keys_expr = Expr(to_string(pkeys));
            }
            else {
                Param_keyss&& pkeyss = _solver_ptr->cparam_keyss();
                keys_expr.reserve(pkeyss.size());
                for (auto&& pkeys : move(pkeyss)) {
                    keys_expr.add_new_expr(to_string(move(pkeys)));
                }
            }
            cout << to_string(keys_expr) << endl;

            cout << std::setprecision(8);
            while (getline(*is_ptr, line)) {
                if (line.empty()) continue;
                State res = _solver_ptr->solve(line);
                cout << res << endl;
            }

            return 0;
        }
        catch (const Error& err) {
            cerr << err << endl;
            return 1;
        }
    }
}
