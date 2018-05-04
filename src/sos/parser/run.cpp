#include "parser/run.hpp"

namespace SOS {
    string Parser::Run::usage() const
    {
        return Util::Run::usage()
               + usage_row('E', "Will preprocess only");
    }

    void Parser::Run::do_stuff()
    {
        Parser parser(*_is_ptr, _preprocess_only);

        if (_preprocess_only) {
            cout << parser.preprocessed_input() << endl;
            return;
        }

        const Parser::Odes& odes_ = parser.codes();
        for (auto& ode_ : odes_) {
            const Ode_key& ode_key_ = code_ode_key(ode_);
            const Dt_keys& dt_keys_ = code_dt_keys(ode_);
            const Ode_spec& ode_spec_ = code_ode_spec(ode_);
            const Param_keys& param_keys_ = code_param_keys(ode_);
            const Const_ids_rows& const_ids_rows_ = code_const_ids_rows(ode_);
            const int steps_ = const_ids_rows_.size();
            const int entries = (steps_ == 0) ? 0
                              : SMT::cconst_ids_row_entries(
                                    const_ids_rows_.front()
                                ).size();
            cerr << ode_key_ << endl;
            cerr << dt_keys_ << endl;
            cerr << ode_spec_ << endl;
            cerr << param_keys_ << endl;
            cerr << steps_ << " " << entries << endl;
            for (auto& row : const_ids_rows_) {
                cerr << SMT::cconst_ids_row_time_consts(row) << endl;
                for (auto& entry : SMT::cconst_ids_row_entries(row)) {
                    cerr << entry << endl;
                }
            }
            cerr << endl;
        }

        cout << parser.csmt_input() << endl;
    }

    string Parser::Run::getopt_str() const noexcept
    {
        return Util::Run::getopt_str() + "E";
    }

    void Parser::Run::process_opt(char c)
    {
        Util::Run::process_opt(c);
        switch (c) {
        case 'E':
            _preprocess_only = true;
            break;
        }
    }
}
