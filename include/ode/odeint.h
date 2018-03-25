#ifndef ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430
#define ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

#include "ode/solver.h"

namespace SOS {
    namespace ODE {
        class Odeint : public Solver {
        public:
            using Times  = vector<Time>;
            using States = vector<State>;

            Odeint(const Ode_spec& ode_spec);

            virtual State solve(const Context& context) final;
        };
    }
}

#endif // ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

