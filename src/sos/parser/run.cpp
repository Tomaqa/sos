#include "parser/run.hpp"

#include <iostream>

namespace SOS {
    using std::cin;
    using std::cout;
    using std::cerr;
    using std::endl;

    int Parser::Run::run(int argc, const char* argv[])
    try {
        Stream_ptr<istream> is_ptr(run_get_istream(argc, argv));

        _parser = Parser(*is_ptr);

        const Parser::Odes& odes_ = _parser.codes();
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

        cout << _parser.csmt_input() << endl;

        return 0;
    }
    catch (const Error& err) {
        cerr << err << endl;
        return 1;
    }
}
