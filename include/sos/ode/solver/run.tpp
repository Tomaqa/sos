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
