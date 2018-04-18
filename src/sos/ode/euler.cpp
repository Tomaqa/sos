#include "ode/euler.hpp"

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
            const Time t_init_ = t_init(context_.ct_init());
            const Time t_end_ = t_end(context_.ct_end());

            for (Time t = t_init_; t < t_end_; t += h) {
                dx += h * f(x, t);
                traject(ode_id_).add_step(x, t);
            }

            return dx;
        }

        State Euler::eval_unif_odes(Dt_ids&& dt_ids_,
                                    Context&& context_) const
        {
            auto f = [this, &dt_ids_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(dt_ids_, dx_, x_, t_);
                     };
            State x = move(context_.cx_init());
            State dx(size());

            const Time h = cstep_size();
            const Time t_init_ = t_init(context_.ct_init());
            const Time t_end_ = t_end(context_.ct_end());

            for (Time t = t_init_; t < t_end_; t += h) {
                f(x, dx, t);
                dx *= h;
                dx += x;
                copy(dx, std::begin(x));
                traject().add_step(x, t);
            }

            return move(dx);
        }

        Time Euler::t_init(const Time t_init_) const
        {
            return t_init_ + cstep_size();
        }

        Time Euler::t_end(const Time t_end_) const
        {
            return t_end_ + cstep_size()/2;
        }
    }
}
