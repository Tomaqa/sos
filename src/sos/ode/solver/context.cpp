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

        Solver::Context::Context(const string& input)
        try
            : Context(Expr(input))
        { }
        catch (const Error& err) {
            throw "Invalid format of input context '"s
                  + input + "':\n" + err;
        }

        Solver::Context::Context(const Expr& expr)
        try {
            expect(expr.size() == 2, "Two top subexpressions expected.");
            expect(!expr[0]->is_token() && expr.cto_expr(0).size() == 2,
                   "Two tokens of time bounds expected.");
            const Expr& t_subexpr = expr.cto_expr(0);
            expect(t_subexpr.is_flat(),
                   "No further subexpressions expected.");
            expect(t_subexpr.cto_token(0).get_value_check<Real>(t_init())
                   && t_subexpr.cto_token(1).get_value_check<Real>(t_end()),
                   "Invalid values of time bounds.");

            expect(!expr[1]->is_token(),
                   "Initial values must be enclosed in subexpression.");
            const Expr& x_subexpr = expr.cto_expr(1);
            expect(x_subexpr.is_flat(),
                   "No further subexpressions expected.");
            x_init() = move(x_subexpr.transform_to_args<Real>());

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
            return move((string)rhs);
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
