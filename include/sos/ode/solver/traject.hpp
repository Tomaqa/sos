#pragma once

#include "sos.hpp"

namespace SOS {
    namespace ODE {
        class Solver::Traject {
        public:
            using Step = pair<Time, State>;
            using Steps = vector<Step>;

            Traject()                                               = default;
            ~Traject()                                              = default;
            Traject(const Traject& rhs)                             = default;
            Traject& operator =(const Traject& rhs)                 = default;
            Traject(Traject&& rhs)                                  = default;
            Traject& operator =(Traject&& rhs)                      = default;

            const Steps& csteps() const;
            explicit operator string () const;
            friend string to_string(const Traject& rhs);
            friend ostream& operator <<(ostream& os, const Traject& rhs);

            size_t size() const                    { return csteps().size(); }

            const auto cbegin() const        { return std::cbegin(csteps()); }
            const auto cend() const            { return std::cend(csteps()); }
            const auto begin() const          { return std::begin(csteps()); }
            const auto end() const              { return std::end(csteps()); }
            auto begin()                      { return std::begin(csteps()); }
            auto end()                          { return std::end(csteps()); }

            void push_back(Step step_)              { add_step(move(step_)); }
            void reserve(size_t size_);
            void clear();

            void init(Param_keys param_keys_, size_t odes_count_);
            void reset(size_t size_);

            void add_step(Step step_);
            void add_step(Time t, State x);
            void add_step(State x, Time t)           { add_step(t, move(x)); }
        protected:
            Steps& steps();
        private:
            Steps _steps;
            Param_keys _param_keys;
            size_t _odes_count;
        };
    }
}
