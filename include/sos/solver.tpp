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
    }

    template <typename OSolver>
    int Solver<OSolver>::csteps() const
    {
        return SMT::cconst_ids_row_entries(
            Parser::code_const_ids_rows(codes().front()).front()
        ).size();
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
        solve_odes(step);
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
        smt_add_conflict(step);
        return do_step(step);
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_get_values(int step)
    {
        Time_const_ids time_consts = SMT::cconst_ids_row_time_consts(
            Parser::code_const_ids_rows(codes().front())[step]
        );
        _time_values = smt_solver().get_step_time_values(time_consts);
        for (auto& ode : codes()) {
            const Const_ids_rows& rows =
                Parser::code_const_ids_rows(ode);
            const Const_ids_row& row = rows[step];
            Const_ids_entries entries = SMT::cconst_ids_row_entries(row);
            _entriess_values.emplace_back(
                smt_solver().get_step_entries_values(entries)
            );
        }
    }

    template <typename OSolver>
    void Solver<OSolver>::solve_odes(int step)
    {
        ODE::Dt_ids dt_ids;
        typename OSolver::Context context;
        for (auto& entries : _entriess_values) {
            auto& entry = entries.front();
            // ! poradi musi odpovidat unif_keys
            dt_ids.push_back(SMT::cconst_values_entry_dt_value(entry));
        }
        _ode_result = code_solver().solve_unif_odes(move(dt_ids),
                                                    move(context));
    }

    template <typename OSolver>
    void Solver<OSolver>::smt_add_asserts(int step)
    {

    }

    template <typename OSolver>
    void Solver<OSolver>::smt_add_conflict(int step)
    {

    }
}
