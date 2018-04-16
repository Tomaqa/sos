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

        // const Parser::Odes_map& odes_map_ = _parser.codes_map();
        // for (auto& odes_p : odes_map_) {
        //     const Ode_key& ode_key_ = odes_p.first;
        //     const Dts_spec_map& ode_spec_ = get<0>(odes_p.second);
        //     const Param_keys& param_keys_ = get<1>(odes_p.second);
        //     const Const_ids& const_ids_ = get<2>(odes_p.second);
        //     const int consts_size = const_ids_.size();
        //     cerr << ode_key_ << endl;
        //     for (auto& ode_p : ode_spec_) {
        //         cerr << ode_p.first << " ";
        //     }
        //     cerr << endl;
        //     for (auto& ode_p : ode_spec_) {
        //         cerr << ode_p.second << " ";
        //     }
        //     cerr << endl;
        //     cerr << param_keys_ << endl;
        //     cerr << consts_size << endl;
        //     for (auto& t : const_ids_) {
        //         cerr << t << endl;
        //     }
        //     cerr << endl;
        // }

        const Parser::Odes& odes_ = _parser.codes();
        for (auto& odes_tup : odes_) {
            const Ode_key& ode_key_ = get<0>(odes_tup);
            const Dt_keys& dt_keys_ = get<1>(odes_tup);
            const Ode_spec& ode_spec_ = get<2>(odes_tup);
            const Param_keys& param_keys_ = get<3>(odes_tup);
            const Const_ids_rows& const_ids_ = get<4>(odes_tup);
            const int consts_size = const_ids_.size();
            cerr << ode_key_ << endl;
            // for (auto& dkey : dt_keys_) {
                // cerr << dkey << " ";
            // }
            // cerr << endl;
            cerr << dt_keys_ << endl;
            // for (auto& dspec : ode_spec_) {
                // cerr << spec << " ";
            // }
            // cerr << endl;
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
