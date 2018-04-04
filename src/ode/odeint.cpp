#include "ode/odeint.hpp"

#include <boost/numeric/odeint/integrate/integrate.hpp>     //< the integrate routines.

namespace SOS {
    namespace ODE {
        namespace odeint = boost::numeric::odeint;

        Real Odeint::solve_ode(Dt_id dt_id_,
                               Context context_, Ode_id ode_id_) const
        {
            State x = move(context_.cx_init());
            // predpokladam ze dx se automaticky alokuje
            // na stejnou velikost jako x
            // -> plytvani
            const Ode_eval& ode_eval_ = codes_eval()[ode_id_];
            auto f = [this, &ode_eval_, dt_id_]
                         (const State& x_, State& dx_, Time t_){
                         eval_ode_step(ode_eval_, dt_id_,
                                       dx_[0], x_, t_);
                     };
            integrate(f, x, move(context_.ct_bounds()));
            return x[0];
        }

        State Odeint::eval_unif_odes(Dt_ids&& dt_ids_,
                                     Context&& context_) const
        {
            State x = move(context_.cx_init());
            // taky plytvani
            // pokud je pocet param. vetsi nez derivaci, ale mensi
            auto f = [this, &dt_ids_](const State& x_, State& dx_, Time t_){
                         eval_unif_odes_step(dt_ids_, dx_, x_, t_);
                     };
            integrate(f, x, move(context_.ct_bounds()));
            return move(x);
        }

        size_t Odeint::integrate(Integrate_f f, State& x,
                                 Interval<Time> t_bounds_) const
        {
            size_t n_steps = odeint::integrate(f, x,
                                               t_bounds_.first,
                                               t_bounds_.second,
                                               step_size()
                                               /*, TObserver(states, times)*/
                                               );
            return n_steps;
        }
    }
}
