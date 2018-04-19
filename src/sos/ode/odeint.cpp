#include "ode/odeint.hpp"

/// Integrate routines
#include <boost/numeric/odeint/integrate/integrate.hpp>

namespace SOS {
    namespace ODE {
        namespace odeint = boost::numeric::odeint;

        Real Odeint::eval_ode(Ode_id ode_id_, Dt_id dt_id_,
                              Context&& context_) const
        {
            State x = move(context_.cx_init());
            auto f = [this, ode_id_, dt_id_]
                         (const State& x_, State& dx_, Time t_){
                         eval_ode_step(ode_id_, dt_id_,
                                       dx_[def_dt_id], x_, t_);
                     };
            integrate(f, x, context_.ct_init(), context_.ct_end(),
                      traject(ode_id_));
            return x[def_dt_id];
        }

        State Odeint::eval_unif_odes(Dt_ids&& dt_ids_,
                                     Context&& context_) const
        {
            State x = move(context_.cx_init());
            auto f = [this, &dt_ids_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(dt_ids_, dx_, x_, t_);
                     };
            integrate(f, x, context_.ct_init(), context_.ct_end(),
                      traject());
            return x;
        }

        size_t Odeint::integrate(Integrate_f f, State& x,
                                 Time t_init_, Time t_end_,
                                 Traject& traject_) const
        {
            auto observer = [&traject_](const State& x_, Time t_){
                traject_.add_step(x_, t_);
            };

            size_t n_steps = odeint::integrate(f, x,
                                               t_init_, t_end_,
                                               cstep_size(),
                                               observer);
            return n_steps;
        }
    }
}
