#include "ode/odeint.h"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

using namespace boost::numeric::odeint;

namespace SOS {
    namespace ODE {
        State Odeint::solve(Context&& context) const
        {
            State x = move(context._x_init);
            /*size_t steps = */
            integrate([&](const State& x_, State& dx, Time t)
                        { eval_ode(context._ode_id, dx, x, t); },
                      x,
                      context._t_bounds.first,
                      context._t_bounds.second,
                      _step_size/*, TObserver(states, times)*/);

            return x;
        }
    }
}
