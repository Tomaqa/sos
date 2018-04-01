#include "ode/odeint.hpp"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

namespace odeint = boost::numeric::odeint;

namespace SOS {
    namespace ODE {
        Real Odeint::solve_ode(Context context_, Ode_id ode_id_) const
        {
            State x = move(context_._x_init);
            const Ode_eval& ode_eval_ = codes_eval()[ode_id_];
            auto f = [this, &ode_eval_, &context_]
                         (const State& x_, State& dx_, Time t_){
                         eval_ode_step(ode_eval_, context_._dt_id,
                                       dx_[0], x_, t_);
                     };
            integrate(f, x, move(context_._t_bounds));
            return x[0];
        }

        State Odeint::solve_unif_odes(Contexts contexts_) const
        {
            State x = move(contexts_._x_init);
            auto f = [this, &contexts_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(contexts_._dt_ids,
                                             dx_, x_, t_);
                     };
            integrate(f, x, move(contexts_._t_bounds));
            return move(x);
        }

        size_t Odeint::integrate(Integrate_f f, State& x,
                                 Interval<Time> t_bounds_) const
        {
            size_t n_steps = odeint::integrate(f, x,
                                               t_bounds_.first,t_bounds_.second,
                                               step_size()
                                               /*, TObserver(states, times)*/);
            return n_steps;
        }
    }
}
