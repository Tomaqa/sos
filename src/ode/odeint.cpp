#include "ode/odeint.h"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

using namespace boost::numeric::odeint;

namespace SOS {
    namespace ODE {
        Odeint::Odeint(const Ode_spec& ode_spec)
        {

        }

        State Odeint::solve(const Context& context)
        {
            State x = context._x_init;
            /*size_t steps = */
            integrate([](const State & x_, State & dx, const Time t){},
                      x,
                      context._t_bounds.first,
                      context._t_bounds.second,
                      _step_size/*, TObserver(states, times)*/);

            return x;
        }
    }
}
