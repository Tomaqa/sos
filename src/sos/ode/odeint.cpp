#include "ode/odeint.hpp"
#include "ode/solver/context.hpp"

/// Integrate routines
#include <boost/numeric/odeint/integrate/integrate.hpp>

namespace SOS {
    namespace ODE {
        namespace odeint = boost::numeric::odeint;

        Real Odeint::eval_ode(Ode_id ode_id_, Dt_id dt_id_,
                              Context&& context_) const
        {
            State x = move(context_.cx_init());
            // predpokladam ze dx se automaticky alokuje
            // na stejnou velikost jako x
            // -> plytvani
            auto f = [this, ode_id_, dt_id_]
                         (const State& x_, State& dx_, Time t_){
                         eval_ode_step(ode_id_, dt_id_,
                                       dx_[def_dt_id], x_, t_);
                     };
            integrate(f, x, context_.ct_init(), context_.ct_end());
            return x[def_dt_id];
        }

        State Odeint::eval_unif_odes(Dt_ids&& dt_ids_,
                                     Context&& context_) const
        {
            State x = move(context_.cx_init());
            // taky plytvani
            // pokud je pocet param. vetsi nez derivaci, ale mensi
            auto f = [this, &dt_ids_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(dt_ids_, std::begin(dx_),
                                             x_, t_);
                     };
            integrate(f, x, context_.ct_init(), context_.ct_end());
            return move(x);
        }

        size_t Odeint::integrate(Integrate_f f, State& x,
                                 Time t_init_, Time t_end_) const
        {
            size_t n_steps = odeint::integrate(f, x,
                                               t_init_, t_end_,
                                               cstep_size()
                                               /*, TObserver(states, times)*/
                                               );
            return n_steps;
        }
    }
}
