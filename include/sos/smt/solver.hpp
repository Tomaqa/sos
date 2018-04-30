#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "smt.hpp"
#include "expr.hpp"

#include <fstream>
// #include <thread>

#include <unistd.h>

namespace SOS {
    namespace SMT {
        using namespace Util;

        using std::endl;

        // using std::thread;

        class Solver {
        public:
            class Run;

            Solver()                                                = default;
            ~Solver();
            Solver(const Solver& rhs)                               = default;
            Solver& operator =(const Solver& rhs)                   = default;
            Solver(Solver&& rhs)                                    = default;
            Solver& operator =(Solver&& rhs)                        = default;
            Solver(string input);

            Sat check_sat();

            Time_const_values
                get_step_time_values(const Time_const_ids& time_consts);
            Const_values_entry
                get_step_entry_values(const Const_ids_entry& const_ids_entry);
            Const_values_entries
                get_step_entries_values(const Const_ids_entries&
                                            const_ids_entries);
        protected:
            void fork_solver();

            // void receiver();

            string get_line();
        private:
            template <typename Arg> Arg get_value(Expr& expr);

            ofstream _ofs;
            string _ofname;

            pid_t _pid;
            int _fd;

            // thread _thread;
        };
    }
}
