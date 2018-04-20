namespace SOS {
    namespace ODE {
        template <typename S>
        void Solver::Run<S>::do_stuff()
        {
            const bool store_traj = !_ofile.empty();

            string line;
            getline(*_is_ptr, line);
            S solver(move(to_string(line)));
            Expr keys_expr;
            const bool unified = solver.is_unified();
            if (unified) {
                const Param_keys& pkeys = solver.cunif_param_keys();
                keys_expr = Expr(to_string(pkeys));
            }
            else {
                Param_keyss&& pkeyss = solver.cparam_keyss();
                for (auto&& pkeys : move(pkeyss)) {
                    keys_expr.add_new_expr(to_string(move(pkeys)));
                }
            }
            cout << to_string(keys_expr) << endl;

            cout << std::setprecision(8);
            while (getline(*_is_ptr, line)) {
                if (line.empty()) continue;
                State res = solver.solve(line);
                cout << res << endl;
                if (!store_traj) continue;
                if (unified) {
                    _ofs << solver.cunif_traject();
                }
                else {
                    _ofs << solver.ctrajects();
                }
                _ofs << endl;
            }
        }
    }
}
