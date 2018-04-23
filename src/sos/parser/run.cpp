#include "parser/run.hpp"

namespace SOS {
    void Parser::Run::do_stuff()
    {
        Parser parser(*_is_ptr, _preprocess_only);

        if (_preprocess_only) {
            cout << parser.preprocessed_input() << endl;
            return;
        }

        const Parser::Odes& odes_ = parser.codes();
        for (auto& odes_tup : odes_) {
            const Ode_key& ode_key_ = get<0>(odes_tup);
            const Dt_keys& dt_keys_ = get<1>(odes_tup);
            const Ode_spec& ode_spec_ = get<2>(odes_tup);
            const Param_keys& param_keys_ = get<3>(odes_tup);
            const Const_ids_rows& const_ids_ = get<4>(odes_tup);
            const int consts_size = const_ids_.size();
            cerr << ode_key_ << endl;
            cerr << dt_keys_ << endl;
            cerr << ode_spec_ << endl;
            cerr << param_keys_ << endl;
            cerr << consts_size << endl;
            for (auto& tup : const_ids_) {
                cerr << tup << endl;
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
