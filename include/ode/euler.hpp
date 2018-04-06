#ifndef ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430
#define ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Euler : public Solver {
        public:
            using Solver::Solver;
        protected:
            virtual Real eval_ode(Dt_id dt_id_, Context&& context_,
                                  Ode_id ode_id_) const override;
        };
    }
}

#endif // ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430

