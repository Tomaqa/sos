#include "ode/euler.hpp"

namespace SOS {
    namespace ODE {
        Real Euler::eval_ode(Dt_id dt_id_, Context&& context_,
                             Ode_id ode_id_) const
        {
            const Ode_eval& ode_eval_ = code_eval(ode_id_);
            State x = move(context_.cx_init());
            Real& dx = x[0];

            const Time h = step_size();
            Time t = context_.ct_init();
            const Time end_t = context_.ct_end() - h/2;

            auto f = [this, &ode_eval_, dt_id_](const State& x_, Time t_){
                         return eval_ode_step(ode_eval_, dt_id_, x_, t_);
                     };

            for (; t < end_t; t += h) {
                dx += h * f(x, t);
            }
            return dx;
        }
    }
}
