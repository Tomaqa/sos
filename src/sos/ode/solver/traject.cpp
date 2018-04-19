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
            return to_string(*this);
        }

        string to_string(const Solver::Traject& rhs)
        {
            string str("");
            str += "t " + SOS::to_string(rhs._param_keys) + "\n";
            for (auto& p : rhs.csteps()) {
                str += std::to_string(p.first) + "\t"
                       + SOS::to_string(p.second)
                       + "\n";
            }
            str += "\n";
            return str;
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

        void Solver::Traject::init(Param_keys param_keys_,
                                   bool has_param_t_)
        {
            if (has_param_t_) param_keys_.pop_back();
            _param_keys = move(param_keys_);
            _has_param_t = has_param_t_;
        }

        void Solver::Traject::reset(size_t size_)
        {
            clear();
            reserve(size_);
        }

        void Solver::Traject::add_step(Step step_)
        {
            if (_has_param_t) step_.second.pop_back();
            steps().emplace_back(move(step_));
        }

        void Solver::Traject::add_step(Time t, State x)
        {
            add_step(make_pair(t, move(x)));
        }
    }
}
