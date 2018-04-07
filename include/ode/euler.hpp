#ifndef ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430
#define ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Euler : public Solver {
        public:
            using Solver::Solver;
        protected:
            virtual Real eval_ode(Ode_id ode_id_, Dt_id dt_id_,
                                  Context&& context_) const override;
            virtual State eval_unif_odes(Dt_ids&& dt_ids_,
                                         Context&& context_) const override;

            template <typename F, typename Ref>
            void integrate(F f, Ref& dx, const State& x,
                           Time t_init_, Time t_end_) const;
        };
    }
}

#endif // ___SOS_EULER_H_OUD4893G789HJ3490G834HG34G3FG430

