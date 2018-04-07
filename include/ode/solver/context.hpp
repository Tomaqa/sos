#pragma once

namespace SOS {
    namespace ODE {
        class Solver::Context {
        public:
            Context()                                               = default;
            ~Context()                                              = default;
            Context(const Context& rhs)                             = default;
            Context& operator =(const Context& rhs)                 = default;
            Context(Context&& rhs)                                  = default;
            Context& operator =(Context&& rhs)                      = default;
            Context(Interval<Time> t_bounds_, State x_init_);
            Context(const string& input);

            explicit operator string () const;
            friend string to_string(const Context& rhs);
            friend ostream& operator <<(ostream& os, const Context& rhs);

            friend bool operator ==(const Context& lhs, const Context& rhs);

            const Interval<Time>& ct_bounds() const      { return _t_bounds; }
            Time ct_init() const                 { return ct_bounds().first; }
            Time ct_end() const                 { return ct_bounds().second; }
            const State& cx_init() const                   { return _x_init; }

            void add_param_t();
        protected:
            void check_values() const;

            Interval<Time>& t_bounds()                   { return _t_bounds; }
            Time& t_init()                        { return t_bounds().first; }
            Time& t_end()                        { return t_bounds().second; }
            State& x_init()                                { return _x_init; }
        private:
            Interval<Time> _t_bounds;
            State _x_init;
        };
    }
}
