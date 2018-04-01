#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        // Solver::Solver(Odes_spec&& odes_spec_)
        Solver::Solver(Odes_spec odes_spec_)
            : _odes_spec(move(odes_spec_)),
              _odes_eval(size())
        {
            std::transform(std::begin(_odes_spec), std::end(_odes_spec),
                           std::begin(_odes_eval),
                           [this](Ode_spec& ode_spec_){
                               return move(create_ode_eval(ode_spec_));
                           });
        }

        void Solver::add_ode_spec(Ode_spec ode_spec_)
        {
            _odes_spec.emplace_back(move(ode_spec_));
            _odes_eval.emplace_back(create_ode_eval(_odes_spec.back()));
        }

        Solver::Ode_eval Solver::create_ode_eval(Ode_spec& ode_spec_)
        {
            Ode_eval ode_eval_(ode_spec_.size());
            std::transform(std::begin(ode_spec_), std::end(ode_spec_),
                           std::begin(ode_eval_),
                           [](Dt_spec& dt_spec_){
                               //! param_keys
                               return move(dt_spec_.get_eval<Real>());
                           });
            return move(ode_eval_);
        }

        // State Solver::solve(const string& input) const
        // {
        //     // regex re("\\s*\\d+\\s*\\((\\s*"s
        //     //          + Expr::re_float + "){2}\\) *\\((\\s*"
        //     //          + Expr::re_float + ")+\\)\\s*");
        //     // if (!regex_match(input, re)) {
        //     //     throw Error("Invalid format of input context: " + input);
        //     // }

        //     Ode_id ode_id;
        //     Interval<Time> t_bounds;

        //     string str;
        //     istringstream iss(input);

        //     iss >> ode_id;
        //     // Expr::flat_extract_braces(iss) >> t_bounds.first >> t_bounds.second;
        //     // iss = Expr::flat_extract_braces(iss);
        //     // State x_init{std::istream_iterator<Real>{iss},
        //                  // std::istream_iterator<Real>{}};
        //     State x_init{};

        //     return solve({ode_id, t_bounds, x_init});
        // }

        // void Solver::eval_ode(Ode_id ode_id,
        //                       State& dx, const State& x, Time t) const
        // {
        //     const auto& ode_eval_ = code_eval(ode_id);
        //     std::transform(std::begin(ode_eval_), std::end(ode_eval_),
        //                    std::begin(dx),
        //                   [this, &x, t](const Dt_eval& dt_eval_){
        //                       return eval_dt(dt_eval_, x, t);
        //                   });
        // }

        // !! ruzne ODE musi mit jednotne parametry!
        void Solver::eval_odes_step(const Dt_ids& dt_ids_,
                                    State& dx, const State& x, Time t) const
        {
            // ! neptat se v kazdem kroku
            function<Real(const Ode_eval& ode_eval_, Dt_id dt_id_)> f;
            if (has_param_t()) {
                f = [this, &x, t](const Ode_eval& ode_eval_, Dt_id dt_id_){
                    return eval_dt_step(ode_eval_[dt_id_], x, t);
                };
            }
            else {
                f = [this, &x](const Ode_eval& ode_eval_, Dt_id dt_id_){
                    return eval_dt_step(ode_eval_[dt_id_], x);
                };
            }
            std::transform(std::begin(codes_eval()), std::end(codes_eval()),
                           std::begin(dt_ids_),
                           std::begin(dx),
                           f);
        }

        void Solver::eval_ode_step(const Ode_eval& ode_eval_, Dt_id dt_id_,
                                   Real& dx, const State& x, Time t) const
        {
            dx = has_param_t(ode_eval_)
                ? eval_dt_step(ode_eval_[dt_id_], x, t)
                : eval_dt_step(ode_eval_[dt_id_], x);
        }

        Real Solver::eval_dt_step(const Dt_eval& dt_eval_,
                                  const State& x, Time t) const
        {
            Dt_eval_params params(x);
            params.emplace_back(t);
            return eval_dt_step(dt_eval_, move(params));
        }
    }
}
