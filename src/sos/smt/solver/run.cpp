#include "smt/solver/run.hpp"

namespace SOS {
    namespace SMT {
        static bool is_prefix(const string& prefix,
                              string::const_iterator str_it)
        {
            return std::mismatch(
                prefix.begin(), prefix.end(), str_it
            ).first == prefix.end();
        }

        void Solver::Run::do_stuff()
        {
            Solver solver("");

            const string check_str = "(check-";
            const string get_str = "(get-";
            string line;
            while (getline(*_is_ptr, line)) {
                if (line.empty()) continue;
                const size_t br_pos = line.find('(');
                if (br_pos == string::npos) {
                    cerr << "Expected command, got: '" << line << "'" << endl;
                    continue;
                }
                solver.command(line);
                if (is_prefix(check_str, line.begin()+br_pos)
                    || is_prefix(get_str, line.begin()+br_pos)) {
                    cout << solver.read_response() << endl;
                }
            }
        }
    }
}
