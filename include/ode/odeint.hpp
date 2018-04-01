#ifndef ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430
#define ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Odeint : public Solver {
        public:
            // virtual State solve(Context context_) const override final;
            virtual Real solve_ode(Ode_id ode_id_, Context context_)
                const override final;
            virtual State solve_odes(Contexts contexts_)
                const override final;
        };
    }
}

#endif // ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

