namespace SOS {
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
            _solver_ptr = new_solver(S(move(to_string(line))));

            while (getline(*is_ptr, line)) {
                if (line.empty()) continue;
                State res = _solver_ptr->solve(line);
                if (stdin) cout << endl << " = ";
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
