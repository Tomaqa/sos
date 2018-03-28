#include "ode/solver.h"
#include "parser.h"

namespace SOS {
    namespace ODE {
        State Solver::solve(const string& input) const
        {
            regex re("\\s*\\d+\\s*\\((\\s*"s
                     + Parser::re_float + "){2}\\) *\\((\\s*"
                     + Parser::re_float + ")+\\)\\s*");
            if (!regex_match(input, re)) {
                throw Error("Invalid format of input context: " + input);
            }

            Ode_id ode_id;
            Interval<Time> t_bounds;

            string str;
            istringstream iss(input);

            iss >> ode_id;
            Parser::flat_extract_braces(iss) >> t_bounds.first >> t_bounds.second;
            iss = Parser::flat_extract_braces(iss);
            State x_init{std::istream_iterator<Value>{iss},
                         std::istream_iterator<Value>{}};

            return solve(Context{ode_id, t_bounds, x_init});
        }

        void Solver::eval_ode(Ode_id ode_id, State& dx, const State& x, Time t) const
        {
            auto& spec = ode_spec(ode_id);
            for (Value& dxi : dx) {
                Dt_id dt_id = &dxi - &dx[0];
                dxi = eval_dt(spec, dt_id, x, t);
            }
        }

        Value Solver::eval_dt(const Ode_spec& ode_spec, Dt_id dt_id,
                              const State& x, Time t) const
        {
            // auto& spec = dt_spec(ode_spec, dt_id);
            return 0.0;
        }
    }
}
