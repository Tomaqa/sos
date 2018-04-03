#ifndef ___SOS_DUMMY_H_OUD4893G789HJ3490G834HG34G3FG430
#define ___SOS_DUMMY_H_OUD4893G789HJ3490G834HG34G3FG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Euler : public Solver {
        public:
            using Solver::Solver;

            virtual Real solve_ode(Dt_id dt_id_,
                                   Context context_,
                                   Ode_id ode_id_ = 0)
                                   const override;
        };
    }
}

#endif // ___SOS_DUMMY_H_OUD4893G789HJ3490G834HG34G3FG430

