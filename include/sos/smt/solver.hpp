#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "smt.hpp"
#include "expr.hpp"

#include <fstream>

#include <unistd.h>

namespace SOS {
    namespace SMT {
        using namespace Util;

        using std::endl;

        class Solver {
        public:
            using Token = Expr::Token;

            class Run;

            Solver()                                                = default;
            ~Solver();
            Solver(const Solver& rhs)                                = delete;
            Solver& operator =(const Solver& rhs)                    = delete;
            Solver(Solver&& rhs);
            Solver& operator =(Solver&& rhs);
            Solver(string input);
            void swap(Solver& rhs);

            void command(string str);
            void command(Expr expr);

            Sat check_sat();

            Time_const_values
                get_step_time_values(const Time_const_ids& time_consts);
            Const_values_entry
                get_step_entry_values(const Const_ids_entry& const_ids_entry);
            Const_values_entries
                get_step_entries_values(const Const_ids_entries&
                                            const_ids_entries);
            Const_values_row
                get_step_row_values(const Const_ids_row& const_ids_row);

            void assert(Expr expr);
            void assert_step_row_values(const Const_ids_row& const_ids_row,
                                        const Const_values_row&
                                            const_values_row,
                                        bool conflict = false);
        protected:
            void check_assert_expr(Expr& expr);
            Expr const_to_assert_expr(Const_id const_id,
                                      Const_value const_value);

            void fork_solver();

            void write_str(string str);
            void write_expr(Expr expr);
            string read_response();
        private:
            template <typename Arg> Arg get_value(Expr& expr);

            string read_line(string begin);
            string read_expr();
            char read_char();

            pid_t _pid{-1};
            int _in_fd{-1};
            int _out_fd{-1};
        };
    }
}
