#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        Solver::Solver(Odes_spec&& odes_spec_)
            : _odes_spec(move(odes_spec_)),
              _odes_eval(size())
        {
            for (auto& ode_spec_ : _odes_spec) {
                Ode_eval ode_eval_(ode_spec_.size());
                std::transform(std::begin(ode_spec_), std::end(ode_spec_),
                               std::begin(ode_eval_),
                               [](auto& dt_spec_){
                                   //! param_keys
                                   // return move(dt_spec.get_eval<Real>());
                                   return Dt_eval(dt_spec_);
                               });
                int i = &ode_spec_ - &_odes_spec[0];
                ode_eval(i) = move(ode_eval_);
            }
        }

        State Solver::solve(const string& input) const
        {
            regex re("\\s*\\d+\\s*\\((\\s*"s
                     + Expr::re_float + "){2}\\) *\\((\\s*"
                     + Expr::re_float + ")+\\)\\s*");
            if (!regex_match(input, re)) {
                throw Error("Invalid format of input context: " + input);
            }

            Ode_id ode_id;
            Interval<Time> t_bounds;

            string str;
            istringstream iss(input);

            iss >> ode_id;
            // Expr::flat_extract_braces(iss) >> t_bounds.first >> t_bounds.second;
            // iss = Expr::flat_extract_braces(iss);
            // State x_init{std::istream_iterator<Real>{iss},
                         // std::istream_iterator<Real>{}};
            State x_init{};

            return solve({ode_id, t_bounds, x_init});
        }

        void Solver::eval_ode(Ode_id ode_id,
                              State& dx, const State& x, Time t) const
        {
            const auto& eval_ = code_eval(ode_id);
            std::transform(std::begin(eval_), std::end(eval_), std::begin(dx),
                          [this, &x, t](const auto& dt_eval_){
                              return eval_dt(dt_eval_, x, t);
                          });
        }

        Real Solver::eval_dt(const Dt_eval& dt_eval_,
                             const State& x, Time t) const
        {
            Dt_params params(x);
            params.emplace_back(t);
            return dt_eval_(move(params));
        }
    }
}
