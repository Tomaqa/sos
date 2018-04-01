#include "ode/odeint.hpp"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

using namespace boost::numeric::odeint;

namespace SOS {
    namespace ODE {
        // State Odeint::solve(Context context_) const
        Real Odeint::solve_ode(Ode_id ode_id_, Context context_) const
        {
            State x = move(context_._x_init);
            const Ode_eval& ode_eval_ = codes_eval()[ode_id_];
            /*size_t steps = */
            integrate([this, &ode_eval_, &context_]
                          (const State& x_, State& dx_, Time t_){
                          // eval_ode(context_._ode_id, dx_, x_, t_);
                          eval_ode_step(ode_eval_, context_._dt_id,
                                        dx_[0], x_, t_);
                      },
                      x,
                      context_._t_bounds.first,
                      context_._t_bounds.second,
                      step_size()/*, TObserver(states, times)*/);
            // return move(x);
            return x[0];
        }

        State Odeint::solve_odes(Contexts contexts_) const
        {
            State x = move(contexts_._x_init);
            /*size_t steps = */
            integrate([this, &contexts_]
                          (const State& x_, State& dx_, Time t_){
                          eval_odes_step(contexts_._dt_ids,
                                         dx_, x_, t_);
                      },
                      x,
                      contexts_._t_bounds.first,
                      contexts_._t_bounds.second,
                      step_size()/*, TObserver(states, times)*/);
            // return move(x);
            return x;
        }
    }
}
