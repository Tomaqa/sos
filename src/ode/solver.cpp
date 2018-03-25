#include "ode/solver.h"

namespace SOS {
    namespace ODE {
        State Solver::solve(const string& input)
        {
            regex re("\\s*\\d+\\s*\\((\\s*"s
                     + re_float + "){2}\\) *\\((\\s*"
                     + re_float + ")+\\)\\s*");
            if (!std::regex_match(input, re)){
                throw Error("Invalid format of input context: " + input);
            }

            Ode_id ode_id;
            Interval<Time> t_bounds;

            string str;
            istringstream iss(input);

            iss >> ode_id;

            iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
            getline(iss, str, ')');
            istringstream(str) >> t_bounds.first >> t_bounds.second;

            iss.ignore(std::numeric_limits<std::streamsize>::max(), '(');
            getline(iss, str, ')');
            iss.clear();
            iss.str(str);
            State x_init{std::istream_iterator<Value>{iss},
                             std::istream_iterator<Value>{}};

            return solve(Context{ode_id, t_bounds, x_init});
        }
    }
}
