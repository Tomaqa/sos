#include "ode/solver.hpp"
#include "ode/solver/traject.hpp"

namespace SOS {
    namespace ODE {
        const Solver::Traject::Steps& Solver::Traject::csteps() const
        {
            return _steps;
        }

        Solver::Traject::Steps& Solver::Traject::steps()
        {
            return _steps;
        }

        Solver::Traject::operator string () const
        {
            return move(to_string(*this));
        }

        string to_string(const Solver::Traject& rhs)
        {
            return move(SOS::to_string(rhs.csteps()));
        }

        ostream& operator <<(ostream& os, const Solver::Traject& rhs)
        {
            return (os << to_string(rhs));
        }

        void Solver::Traject::reserve(size_t size_)
        {
            steps().reserve(size_);
        }

        void Solver::Traject::clear()
        {
            steps().clear();
        }

        void Solver::Traject::init(size_t size_)
        {
            clear();
            reserve(size_);
        }

        void Solver::Traject::add_step(Step step_)
        {
            steps().emplace_back(move(step_));
        }

        void Solver::Traject::add_step(Time t, State x)
        {
            add_step(make_pair(t, move(x)));
        }
    }
}
