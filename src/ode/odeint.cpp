#include "ode/odeint.hpp"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

using namespace boost::numeric::odeint;

namespace SOS {
    namespace ODE {
        State Odeint::solve(Context context_) const
        {
            State x = move(context_._x_init);
            /*size_t steps = */
            integrate([&](const State& x_, State& dx_, Time t_)
                        { eval_ode(context_._ode_id, dx_, x_, t_); },
                      x,
                      context_._t_bounds.first,
                      context_._t_bounds.second,
                      step_size()/*, TObserver(states, times)*/);

            return move(x);
        }
    }
}
