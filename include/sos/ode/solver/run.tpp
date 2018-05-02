namespace SOS {
    namespace ODE {
        template <typename S>
        void Solver::Run<S>::do_stuff()
        {
            const bool store_traj = !_ofile.empty();

            string line;
            getline(*_is_ptr, line);
            S solver(move(to_string(line)));
            const bool unified = solver.is_unified();
            if (unified) {
                const Param_keys& pkeys = solver.cunif_param_keys();
                cout << to_string(Expr(to_string(pkeys)));
                auto& pkeyss_ids = solver.cunif_param_keyss_ids();
                if (!pkeyss_ids.empty()) {
                    Expr pkeyss_ids_expr;
                    for (auto& pkeys_ids : pkeyss_ids) {
                        Expr pkeys_ids_expr;
                        for (auto pkey_id : pkeys_ids) {
                            pkeys_ids_expr.add_new_etoken(pkey_id);
                        }
                        pkeyss_ids_expr.add_new_expr(move(pkeys_ids_expr));
                    }
                    cout << " " << to_string(pkeyss_ids_expr);
                }
            }
            else {
                Param_keyss&& pkeyss = solver.cparam_keyss();
                Expr keys_expr;
                for (auto&& pkeys : move(pkeyss)) {
                    keys_expr.add_new_expr(to_string(move(pkeys)));
                }
                cout << to_string(keys_expr);
            }
            cout << endl;

            cout << std::setprecision(double_precision) << std::fixed;
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
