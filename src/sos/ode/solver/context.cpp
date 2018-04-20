#include "ode/solver.hpp"
#include "ode/solver/context.hpp"

namespace SOS {
    namespace ODE {
        Solver::Context::Context(Interval<Time> t_bounds_, State x_init_)
            : _t_bounds(move(t_bounds_)),
              _x_init(move(x_init_))
        {
            check_values();
        }

        Solver::Context::Context(string input)
        try
            : Context(Expr(move(input)))
        { }
        catch (const Error& err) {
            throw "Invalid format of input context '"s
                  + input + "':\n" + err;
        }

        Solver::Context::Context(Expr expr)
        try {
            expect(expr.size() == 2 && expr.is_deep(),
                   "Two top subexpressions expected.");

            // Expr& t_subexpr = expr.to_expr(0);
            // auto it = expr.begin();
            // Expr& t_subexpr = expr.to_expr(it);
            Expr& t_subexpr = expr.get_expr();
            expect(t_subexpr.size() == 2 && t_subexpr.is_flat(),
                   "Two tokens of time bounds expected.");
            // expect(t_subexpr.to_etoken(0).get_value_valid<Real>(t_init())
            //        && t_subexpr.to_etoken(1).get_value_valid<Real>(t_end()),
            // auto sit = t_subexpr.begin();
            // expect(t_subexpr.to_etoken(sit).get_value_valid<Real>(t_init())
            //        && t_subexpr.to_etoken(++sit).get_value_valid<Real>(t_end()),
            expect(t_subexpr.get_etoken().get_value_valid<Real>(t_init())
                   && t_subexpr.get_etoken().get_value_valid<Real>(t_end()),
                   "Invalid values of time bounds.");

            // x_init() = expr.to_expr(1).transform_to_args<Real>();
            // x_init() = expr.to_expr(++it).transform_to_args<Real>();
            x_init() = expr.get_expr().transform_to_args<Real>();

            check_values();
        }
        catch (const Error& err) {
            throw "Invalid format of input context '"s
                  + to_string(expr) + "':\n" + err;
        }

        void Solver::Context::check_values() const
        {
            expect(ct_init() <= ct_end(),
                   "Invalid time interval: "s
                   + std::to_string(ct_init()) + ", "
                   + std::to_string(ct_end()));
        }

        Solver::Context::operator string () const
        {
            return "( "s + SOS::to_string(ct_bounds()) + " )"
                   + " ( " + SOS::to_string(cx_init()) + ")";
        }

        string to_string(const Solver::Context& rhs)
        {
            return (string)rhs;
        }

        ostream& operator <<(ostream& os, const Solver::Context& rhs)
        {
            return (os << to_string(rhs));
        }

        bool operator ==(const Solver::Context& lhs,
                         const Solver::Context& rhs)
        {
            return lhs.ct_bounds() == rhs.ct_bounds()
                && lhs.cx_init() == rhs.cx_init();
        }

        void Solver::Context::add_param_t()
        {
            x_init().emplace_back(ct_init());
        }
    }
}
