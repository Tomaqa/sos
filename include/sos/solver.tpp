#include <iostream>

namespace SOS {
    using std::cout;
    using std::cerr;
    using std::endl;

    template <typename OSolver>
    Solver<OSolver>::Solver(istream& is)
        : _parser(is)
    {
        init();
    }

    template <typename OSolver>
    Solver<OSolver>::Solver(string input)
        : _parser(move(input))
    {
        init();
    }

    template <typename OSolver>
    void Solver<OSolver>::init()
    {
        _smt_solver = SMT::Solver(cparser().csmt_input());

        Odes_spec odes_spec;
        Param_keyss param_keyss;
        odes_spec.reserve(codes().size());
        param_keyss.reserve(codes().size());
        for (auto& ode : codes()) {
            odes_spec.emplace_back(Parser::code_ode_spec(ode));
            param_keyss.emplace_back(Parser::code_param_keys(ode));
        }
        _ode_solver = OSolver(move(odes_spec), move(param_keyss), true);

        _odes_row_values.reserve(codes().size());
        _ode_results.resize(codes().size());
    }

    template <typename OSolver>
    int Solver<OSolver>::csteps() const
    {
        return cconst_ids_rows(0).size();
    }

    template <typename OSolver>
    int Solver<OSolver>::cconst_entries_count() const
    {
        return SMT::cconst_ids_row_entries(cconst_ids_row(0, 0)).size();
    }

    template <typename OSolver>
    const typename Solver<OSolver>::Const_ids_rows&
        Solver<OSolver>::cconst_ids_rows(const Ode& ode)
    {
        return Parser::code_const_ids_rows(ode);
    }

    template <typename OSolver>
    const typename Solver<OSolver>::Const_ids_rows&
        Solver<OSolver>::cconst_ids_rows(int ode_id) const
    {
        return cconst_ids_rows(codes()[ode_id]);
    }

    template <typename OSolver>
    const typename Solver<OSolver>::Const_ids_row&
        Solver<OSolver>::cconst_ids_row(const Ode& ode, int step)
    {
        return cconst_ids_rows(ode)[step];
    }

    template <typename OSolver>
    const typename Solver<OSolver>::Const_ids_row&
        Solver<OSolver>::cconst_ids_row(int ode_id, int step) const
    {
        return cconst_ids_rows(ode_id)[step];
    }

    template <typename OSolver>
    void Solver<OSolver>::set_traject_ofile(string ofile)
    {
        _traj_ofs = ofstream(move(ofile));
    }

    template <typename OSolver>
    typename Solver<OSolver>::Sat Solver<OSolver>::solve()
    {
        const bool sat = do_step(0);
        return sat ? Sat::sat : Sat::unsat;
    }

    template <typename OSolver>
    bool Solver<OSolver>::do_step(int step)
    {
        cout << endl << "Step " << step << " ..." << endl;
        const Sat sat = smt_check_sat();
        expect(sat != Sat::unknown, "unknown");
        if (sat == Sat::unsat) {
            return backtrack(step);
        }
        if (step == csteps()) {
            return true;
        }
        smt_get_values(step);
        solve_odes();
        smt_add_asserts(step);
        return do_step(step+1);
    }

    template <typename OSolver>
    typename Solver<OSolver>::Sat Solver<OSolver>::smt_check_sat()
    {
        return smt_solver().check_sat();
    }

    template <typename OSolver>
    bool Solver<OSolver>::backtrack(int step)
    {
        if (step == 0) return false;
        cout << "Backtrack ..." << endl;
        --step;
        smt_add_conflict();
        return do_step(step);
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_get_values(int step)
    {
        _odes_row_values.clear();
        for (auto& ode : codes()) {
            const Const_ids_row& row_ids = cconst_ids_row(ode, step);
            Const_values_row row_vals =
                smt_solver().get_step_row_values(row_ids);
            _odes_row_values.emplace_back(move(row_vals));
        }
    }

    template <typename OSolver>
    void Solver<OSolver>::solve_odes()
    {
        const int odes_count = codes().size();
        const int entries_count = cconst_entries_count();
        Ode_results trans_ode_results;
        trans_ode_results.reserve(entries_count);
        for (int e = 0; e < entries_count; e++) {
            ODE::Dt_ids dt_ids;
            typename OSolver::Contexts ctxs;
            dt_ids.reserve(odes_count);
            ctxs.reserve(odes_count);
            for (int o = 0; o < odes_count; o++) {
                const Const_values_row& row_vals = _odes_row_values[o];
                const Time_const_values& time_values =
                    SMT::cconst_values_row_time_values(row_vals);
                const Const_values_entries& entries_vals =
                    SMT::cconst_values_row_entries(row_vals);
                const Const_values_entry& entry_vals = entries_vals[e];
                ODE::State state;
                auto& param_values =
                    SMT::cconst_values_entry_param_values(entry_vals);
                state.reserve(param_values.size()+1);
                dt_ids.push_back(
                    SMT::cconst_values_entry_dt_value(entry_vals)
                );
                state.push_back(
                    SMT::cconst_values_entry_init_value(entry_vals)
                );
                copy(param_values, std::back_inserter(state));
                ctxs.emplace_back(time_values, move(state));
            }
            Ode_result res = code_solver().solve_odes(move(dt_ids),
                                                      move(ctxs));
            trans_ode_results.emplace_back(move(res));
        }

        for (int o = 0; o < odes_count; o++) {
            _ode_results[o].clear();
            _ode_results[o].reserve(entries_count);
            for (int e = 0; e < entries_count; e++) {
                _ode_results[o].push_back(trans_ode_results[e][o]);
            }
        }

        if (_traj_ofs) {
            _traj_ofs << code_solver().cunif_traject() << endl;
        }
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_add_asserts(int step)
    {
        const int odes_size = codes().size();
        for (int o = 0; o < odes_size; o++) {
            const Const_ids_row& row_ids = cconst_ids_row(o, step);
            const Const_values_row& row_vals = _odes_row_values[o];
            const Ode_result& ode_res = _ode_results[o];
            smt_solver().assert_step_row(row_ids, row_vals, ode_res);
        }
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_add_conflict()
    {
        smt_solver().assert_last_step_row_conflict();
    }
}
