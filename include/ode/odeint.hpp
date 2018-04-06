#ifndef ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430
#define ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

#include "ode/solver.hpp"

namespace SOS {
    namespace ODE {
        class Odeint : public Solver {
        public:
            using Solver::Solver;
        protected:
            using Integrate_f = function<void(const State&, State&, Time)>;

            virtual Real eval_ode(Dt_id dt_id_, Context&& context_,
                                  Ode_id ode_id_) const override;
            virtual State eval_unif_odes(Dt_ids&& dt_ids_,
                                         Context&& context_)
                                         const override final;

            size_t integrate(Integrate_f f, State& x,
                             Time t_init_, Time t_end_) const;
        };
    }
}

#endif // ___SOS_ODEINT_H_OUD48937GH34789GH349GHJY54HFG430

