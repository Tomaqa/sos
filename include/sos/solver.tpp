#include <iostream>
#include <iomanip>

#ifdef PROFILE
#include <omp.h>

extern double wall_time;
extern double check_sat_time;
extern double other_smt_time;
extern double ode_time;
#endif //< PROFILE

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

        if (cparser().is_ode_step_set()) {
            _ode_solver.set_step_size(cparser().code_step());
        }

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
    void Solver<OSolver>::print_results()
    {
        if (is_quiet()) return;
        const Time_const_ids& init_time_ids =
            SMT::cconst_ids_row_time_consts(cconst_ids_row(0, 0));
        const Time_const_ids& end_time_ids =
            SMT::cconst_ids_row_time_consts(cconst_ids_row(0, csteps()-1));
        const Time_const_value init_t =
            smt_solver().get_step_time_values(init_time_ids).first;
        const Time_const_value end_t =
            smt_solver().get_step_time_values(end_time_ids).first;

        cout << endl;
        const int odes_count = codes().size();
        const int entries_count = cconst_entries_count();
        for (int e = 0; e < entries_count; e++) {
            for (int o = 0; o < odes_count; o++) {
                const Const_ids_entry& init_entry =
                    SMT::cconst_ids_row_entries(cconst_ids_row(o, 0))[e];
                const Const_ids_entry& end_entry =
                    SMT::cconst_ids_row_entries(
                        cconst_ids_row(o, csteps()-1)
                    )[e];
                const Init_const_id& init_const =
                    SMT::cconst_ids_entry_init_const(init_entry);
                const Init_const_id& end_const =
                    SMT::cconst_ids_entry_init_const(end_entry);
                const Init_const_value init_val =
                    SMT::cconst_values_entry_init_value(
                        smt_solver().get_step_entry_values(init_entry)
                    );
                const Init_const_value end_val =
                    SMT::cconst_values_entry_init_value(
                        smt_solver().get_step_entry_values(end_entry)
                    );

                cout << init_const << "(" << init_t << ") = " << init_val
                     << "  -->  "
                     << end_const << "(" << end_t << ") = " << end_val
                     << endl;
            }
            if (e < entries_count-1) cout << endl;
        }

        #ifdef PROFILE
        const double smt_time = check_sat_time + other_smt_time;
        const double smt_rel_time = (smt_time/wall_time)*100;
        const double check_sat_rel_time = (check_sat_time/smt_time)*100;
        const double other_smt_time = smt_time - check_sat_time;
        const double other_smt_rel_time = 100. - check_sat_rel_time;
        const double ode_rel_time = (ode_time/wall_time)*100;
        const double other_time = wall_time - smt_time - ode_time;
        const double other_rel_time = 100. - smt_rel_time - ode_rel_time;

        cout << std::setprecision(3) << endl
             << "Wall time: " << wall_time << "s\n"
             << "SMT time: " << smt_time << "s"
             << " (" << smt_rel_time << " %)" << endl
             << "    " << "check-sat time: " << check_sat_time << "s"
                       << " (" << check_sat_rel_time << " %)" << endl
             << "    " << "other SMT time: " << other_smt_time << "s"
                       << " (" << other_smt_rel_time << " %)" << endl
             << "ODE time: " << ode_time << "s"
             << " (" << ode_rel_time << " %)" << endl
             << "Other time: " << other_time << "s"
             << " (" << other_rel_time << " %)" << endl;
        #endif //< PROFILE
    }

    template <typename OSolver>
    void Solver<OSolver>::set_traject_ofile(string ofile)
    {
        _traj_ofs = ofstream(move(ofile));
    }

    template <typename OSolver>
    typename Solver<OSolver>::Sat Solver<OSolver>::solve()
    {
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE
        const bool sat = do_step(0);
        #ifdef PROFILE
        wall_time = omp_get_wtime() - ts;
        #endif //< PROFILE
        return sat ? Sat::sat : Sat::unsat;
    }

    template <typename OSolver>
    bool Solver<OSolver>::do_step(int step)
    {
        if (is_verbose()) {
            cout << endl << "Step " << step << " ..." << endl;
        }

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
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE
        const Sat sat = smt_solver().check_sat();
        #ifdef PROFILE
        const double time_ = omp_get_wtime() - ts;
        check_sat_time += time_;
        #endif //< PROFILE
        return sat;
    }

    template <typename OSolver>
    bool Solver<OSolver>::backtrack(int step)
    {
        if (step == 0) return false;
        if (is_verbose()) {
            cout << "Backtrack ..." << endl;
        }
        smt_add_conflict();
        return do_step(step-1);
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_get_values(int step)
    {
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE
        _odes_row_values.clear();
        for (auto& ode : codes()) {
            const Const_ids_row& row_ids = cconst_ids_row(ode, step);
            Const_values_row row_vals =
                smt_solver().get_step_row_values(row_ids);
            _odes_row_values.emplace_back(move(row_vals));
        }
        #ifdef PROFILE
        other_smt_time += omp_get_wtime() - ts;
        #endif //< PROFILE
    }

    template <typename OSolver>
    void Solver<OSolver>::solve_odes()
    {
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE

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

        #ifdef PROFILE
        ode_time += omp_get_wtime() - ts;
        #endif //< PROFILE

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
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE
        const int odes_size = codes().size();
        for (int o = 0; o < odes_size; o++) {
            const Const_ids_row& row_ids = cconst_ids_row(o, step);
            const Const_values_row& row_vals = _odes_row_values[o];
            const Ode_result& ode_res = _ode_results[o];
            smt_solver().assert_step_row(row_ids, row_vals, ode_res);
        }
        #ifdef PROFILE
        other_smt_time += omp_get_wtime() - ts;
        #endif //< PROFILE
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_add_conflict()
    {
        #ifdef PROFILE
        const double ts = omp_get_wtime();
        #endif //< PROFILE
        smt_solver().assert_last_step_row_conflict();
        #ifdef PROFILE
        other_smt_time += omp_get_wtime() - ts;
        #endif //< PROFILE
    }
}
