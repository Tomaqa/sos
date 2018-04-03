#include "ode/euler.hpp"

namespace SOS {
    namespace ODE {
        Real Euler::solve_ode(Dt_id dt_id_,
                              Context context_, Ode_id ode_id_) const
        {
            const Ode_eval& ode_eval_ = codes_eval()[ode_id_];
            State x = move(context_.cx_init());
            Real& dx = x[0];
            const Time h = step_size();
            auto f = [this, &ode_eval_, dt_id_](const State& x_, Time t_){
                         return eval_ode_step(ode_eval_, dt_id_, x_, t_);
                     };

            for (Real t = context_.ct_init(), et = context_.ct_end();
                 t < et; t += h) {
                dx += h * f(x, t);
            }

            return dx;
        }
    }
}
