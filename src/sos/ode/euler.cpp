#include "ode/euler.hpp"
#include "ode/solver/context.hpp"

namespace SOS {
    namespace ODE {
        Real Euler::eval_ode(Ode_id ode_id_, Dt_id dt_id_,
                             Context&& context_) const
        {
            auto f = [this, ode_id_, dt_id_](const State& x_, Time t_){
                         return eval_ode_step(ode_id_, dt_id_, x_, t_);
                     };
            State x = move(context_.cx_init());
            Real& dx = x[def_dt_id];

            const Time h = cstep_size();
            const Time t_init_ = context_.ct_init();
            const Time t_end_ = t_end(context_.ct_end());

            for (Time t = t_init_; t < t_end_; t += h) {
                dx += h * f(x, t);
            }

            return dx;
        }

        State Euler::eval_unif_odes(Dt_ids&& dt_ids_,
                                    Context&& context_) const
        {
            auto f = [this, &dt_ids_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(dt_ids_, dx_, x_, t_);
                         // return dx_;
                     };
            State x = move(context_.cx_init());
            // State dx(std::begin(x), std::begin(x)+size());
            State dx(size());

            const Time h = cstep_size();
            const Time t_init_ = context_.ct_init();
            const Time t_end_ = t_end(context_.ct_end());

            for (Time t = t_init_; t < t_end_; t += h) {
                // dx += h * f(x, t);
                // dx += h * f(x, dx, t);
                // dx = dx + h * f(x, t);
                f(x, dx, t);
                // dx += h * dx;
                dx *= h;
                dx += x;
                copy(dx, std::begin(x));
            }

            return move(dx);
        }

        Time Euler::t_end(const Time t_end_) const
        {
            return t_end_ - cstep_size()/2;
        }
    }
}
