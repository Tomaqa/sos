#ifndef ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430
#define ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Odeint : public Solver {
        public:
            virtual Real solve_ode(Context context_, Ode_id ode_id_ = 0)
                const override final;
            virtual State solve_unif_odes(Contexts contexts_)
                const override final;
        protected:
            using Integrate_f = function<void(const State&, State&, Time)>;

            size_t integrate(Integrate_f f, State& x,
                             Interval<Time> t_bounds_) const;
        };
    }
}

#endif // ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

