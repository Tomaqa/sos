#include "parser/run.hpp"

namespace SOS {
    void Parser::Run::do_stuff()
    {

        list<string> l1;
        auto it = l1.end();
        cout << (it == l1.end()) << endl;
        l1.push_back("a");
        cout << (it == l1.end()) << endl;
        if (it == l1.end()) {
            it = l1.begin();
        }
        cout << *it << endl;


        return;

        Parser parser(*_is_ptr);

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
}
