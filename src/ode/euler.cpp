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
            integrate(f, dx, x, context_.ct_init(), context_.ct_end());
            return dx;
        }

        State Euler::eval_unif_odes(Dt_ids&& dt_ids_,
                                    Context&& context_) const
        {
            auto f = [this, &dt_ids_](const State& x_, Time t_){
                         return eval_unif_odes_step(dt_ids_, x_, t_);
                     };
            State x = move(context_.cx_init());
            State& dx = x;
            integrate(f, dx, x, context_.ct_init(), context_.ct_end());
            return move(dx);
        }

        template <typename F, typename Ref>
        void Euler::integrate(F f, Ref& dx, const State& x,
                              Time t_init_, Time t_end_) const
        {
            const Time h = cstep_size();
            t_end_ -= h/2;

            for (Time t = t_init_; t < t_end_; t += h) {
                dx += h * f(x, t);
            }
        }
    }
}
