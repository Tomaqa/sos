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
        Solver(istream& is, bool parse_only = false);
        Solver(string input, bool parse_only = false);

        void be_verbose()                                 { _verbose = true; }
        void be_quiet()                                     { _quiet = true; }

        bool is_verbose() const                           { return _verbose; }
        bool is_quiet() const                               { return _quiet; }

        string smt_input() const;

        void print_results();
        #ifdef PROFILE
        void print_profile() const;
        #endif //< PROFILE

        void set_traject_ofile(string ofile);

        Sat solve();
    protected:
        using Ode_spec = ODE::Ode_spec;
        using Odes_spec = ODE::Odes_spec;
        using Param_keys = ODE::Param_keys;
        using Param_keyss = ODE::Param_keyss;
        using Ode = Parser::Ode;
        using Odes = Parser::Odes;

        using Const_id = SMT::Const_id;
        using Const_ids = SMT::Const_ids;
        using Time_const_id = SMT::Time_const_id;
        using Time_const_ids = SMT::Time_const_ids;
        using Dt_const_id = SMT::Dt_const_id;
        using Init_const_id = SMT::Init_const_id;
        using Const_ids_entry = SMT::Const_ids_entry;
        using Const_ids_entries = SMT::Const_ids_entries;
        using Const_ids_row = SMT::Const_ids_row;
        using Const_ids_rows = SMT::Const_ids_rows;

        using Const_value = SMT::Const_value;
        using Const_values = SMT::Const_values;
        using Time_const_value = SMT::Time_const_value;
        using Time_const_values = SMT::Time_const_values;
        using Dt_const_value = SMT::Dt_const_value;
        using Init_const_value = SMT::Init_const_value;
        using Const_values_entry = SMT::Const_values_entry;
        using Const_values_entries = SMT::Const_values_entries;
        using Const_values_row = SMT::Const_values_row;
        using Const_values_rows = SMT::Const_values_rows;

        using Ode_result = ODE::State;
        using Ode_results = vector<Ode_result>;

        void init(bool parse_only);

        const Parser& cparser() const                      { return _parser; }
        const Odes& codes() const                { return cparser().codes(); }
        int csteps() const;
        int cconst_entries_count() const;

        const SMT::Solver& csmt_solver() const         { return _smt_solver; }
        SMT::Solver& smt_solver()                      { return _smt_solver; }

        const OSolver& code_solver() const             { return _ode_solver; }
        OSolver& ode_solver()                          { return _ode_solver; }

        static const Const_ids_rows& cconst_ids_rows(const Ode& ode);
        const Const_ids_rows& cconst_ids_rows(int ode_id) const;
        static const Const_ids_row& cconst_ids_row(const Ode& ode, int step);
        const Const_ids_row& cconst_ids_row(int ode_id, int step) const;

        bool do_step(int step);
        Sat smt_check_sat();
        bool backtrack(int step);
        void smt_get_values(int step);
        void solve_odes();
        void smt_add_asserts(int step);
        void smt_add_conflict();
    private:
        Parser _parser;
        SMT::Solver _smt_solver;
        OSolver _ode_solver;

        Const_values_rows _odes_row_values;
        Ode_results _ode_results;

        bool _verbose{false};
        bool _quiet{false};

        ofstream _traj_ofs;
    };

}

#include "solver.tpp"
