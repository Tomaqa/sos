#pragma once

#include "sos.hpp"
#include "util.hpp"
#include "smt.hpp"
#include "expr.hpp"

#include <fstream>
#include <stack>

#include <cmath>
#include <unistd.h>

namespace SOS {
    namespace SMT {
        using namespace Util;

        using std::endl;

        using std::stack;

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
            void swap(Solver& rhs);
            Solver(string input);

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

            void assert(Expr_place&& place);
            void assert_step_row(const Const_ids_row& const_ids_row,
                                 const Const_values_row& const_values_row,
                                 const Const_values& ode_result);
            void assert_last_step_row_conflict();
        protected:
            using Asserts = Expr::Exprs;
            using Asserts_stack = stack<Asserts>;

            Asserts_stack& asserts_stack()          { return _asserts_stack; }
            bool asserts_empty();
            void push_asserts(Asserts asserts = {});
            void pop_asserts();
            Asserts& last_asserts();

            Expr make_assert_step_row_expr(const Const_ids_row& const_ids_row,
                                           const Const_values_row&
                                               const_values_row);
            void add_step_entry_asserts(const Const_ids_entry&
                                            const_ids_entry,
                                        const Const_values_entry&
                                            const_values_entry,
                                        Expr& expr);
            void add_step_ode_result_asserts(const Const_ids_row&
                                                 const_ids_row,
                                             const Const_values& ode_result,
                                             Expr& expr);

            Expr const_to_assert_expr(Const_id const_id,
                                      Const_value const_value);
            Expr expr_to_assert_expr(Expr expr,
                                     Const_value const_value);

            void fork_solver();

            void write_str(string str);
            void write_expr(Expr expr);
            string read_response();
        private:
            static constexpr const int ode_result_precision_dec = 4;
            static constexpr const int ode_result_precision =
                double_precision - ode_result_precision_dec;
                static_assert(ode_result_precision > 0,
                              "Invalid ODE results precision");
            static constexpr const double ode_result_fact =
                pow(10, ode_result_precision);

            template <typename Arg> Arg get_value(Expr& expr);

            Expr eplace_to_assert_expr(Expr::Expr_place_ptr place_ptr,
                                       Const_value const_value);

            static Const_value round_ode_result(Const_value value);

            string read_line(string begin);
            string read_expr();
            char read_char();

            pid_t _pid{-1};
            int _in_fd{-1};
            int _out_fd{-1};

            ofstream _log_ofs;

            int _assert_step_cnt{0};
            Asserts_stack _asserts_stack;
            Asserts _prev_last_asserts;
        };
    }
}
