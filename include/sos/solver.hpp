#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "parser.hpp"
#include "smt/solver.hpp"
#include "ode/solver.hpp"

namespace SOS {
    using namespace Util;

    template <typename OSolver>
    class Solver {
    public:
        using Sat = SMT::Sat;

        class Run;

        Solver()                                                    = default;
        ~Solver()                                                   = default;
        Solver(const Solver& rhs)                                   = default;
        Solver& operator =(const Solver& rhs)                       = default;
        Solver(Solver&& rhs)                                        = default;
        Solver& operator =(Solver&& rhs)                            = default;
        Solver(istream& is);
        Solver(string input);

        Sat solve();
    protected:
        using Ode_spec = ODE::Ode_spec;
        using Odes_spec = ODE::Odes_spec;
        using Param_keys = ODE::Param_keys;
        using Param_keyss = ODE::Param_keyss;
        using Odes = Parser::Odes;

        using Const_id = SMT::Const_id;
        using Const_ids = SMT::Const_ids;
        using Time_const_ids = SMT::Time_const_ids;
        using Dt_const_id = SMT::Dt_const_id;
        using Init_const_id = SMT::Init_const_id;
        using Const_ids_entry = SMT::Const_ids_entry;
        using Const_ids_entries = SMT::Const_ids_entries;
        using Const_ids_row = SMT::Const_ids_row;
        using Const_ids_rows = SMT::Const_ids_rows;

        using Const_value = SMT::Const_value;
        using Const_values = SMT::Const_values;
        using Time_const_values = SMT::Time_const_values;
        using Dt_const_value = SMT::Dt_const_value;
        using Init_const_value = SMT::Init_const_value;
        using Const_values_entry = SMT::Const_values_entry;
        using Const_values_entries = SMT::Const_values_entries;

        using Const_values_entriess = vector<Const_values_entries>;

        using Unif_param_keyss_ids = typename OSolver::Unif_param_keyss_ids;
        using Ode_result = ODE::State;
        using Ode_results = vector<Ode_result>;

        void init();

        const Parser& cparser() const                      { return _parser; }
        const Odes& codes() const                { return cparser().codes(); }
        int csteps() const;
        int cconst_entries_count() const;

        const SMT::Solver& csmt_solver() const         { return _smt_solver; }
        SMT::Solver& smt_solver()                      { return _smt_solver; }

        const OSolver& code_solver() const             { return _ode_solver; }
        OSolver& ode_solver()                          { return _ode_solver; }
        const Unif_param_keyss_ids& cunif_param_keyss_ids()
                             { return code_solver().cunif_param_keyss_ids(); }

        bool do_step(int step);
        Sat smt_check_sat();
        bool backtrack(int step);
        void smt_get_values(int step);
        void solve_odes(int step);
        void smt_add_asserts(int step);
        void smt_add_conflict(int step);
    private:
        Parser _parser;
        SMT::Solver _smt_solver;
        OSolver _ode_solver;

        Time_const_values _time_values;
        // Const_values_entries _entries_values;
        Const_values_entriess _entriess_values;
        // Ode_result _ode_result;
        Ode_results _ode_results;

    };

}

#include "solver.tpp"