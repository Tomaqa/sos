#include "smt/solver.hpp"
#include "expr/eval.hpp"
#include "parser.hpp"

#include <sys/wait.h>

namespace SOS {
    namespace SMT {
        Solver::~Solver()
        {
            if (_in_fd >= 0) close(_in_fd);
            if (_out_fd >= 0) close(_out_fd);
            if (_pid >= 0) waitpid(_pid, NULL, 0);
        }

        Solver::Solver(Solver&& rhs)
            : _pid(rhs._pid),
              _in_fd(rhs._in_fd),
              _out_fd(rhs._out_fd),
              _log_ofs(move(rhs._log_ofs))
        {
            rhs._pid = rhs._in_fd = rhs._out_fd = -1;
        }

        Solver& Solver::operator =(Solver&& rhs)
        {
            Solver tmp(move(rhs));
            swap(tmp);
            return *this;
        }

        void Solver::swap(Solver& rhs)
        {
            std::swap(_pid, rhs._pid);
            std::swap(_in_fd, rhs._in_fd);
            std::swap(_out_fd, rhs._out_fd);
            std::swap(_log_ofs, rhs._log_ofs);
        }

        Solver::Solver(string input)
            : _log_ofs("local/log.smt2")
        {
            fork_solver();
            write_str(move(input));
        }

        void Solver::command(string str)
        {
            write_str(move(str));
        }

        void Solver::command(Expr expr)
        {
            write_expr(move(expr));
        }

        Sat Solver::check_sat()
        {
            _assert_step_cnt = 0;
            write_str("(check-sat)");
            string res = read_response();
            if (res == "sat") return Sat::sat;
            if (res == "unsat") return Sat::unsat;
            expect(res == "unknown",
                   "Unexpected output of SMT solver:\n" + res);
            return Sat::unknown;
        }

        Time_const_values
            Solver::get_step_time_values(const Time_const_ids& time_consts)
        {
            write_str("(get-value ("s
                       + to_string(time_consts.first)
                       + " "
                       + to_string(time_consts.second)
                       + "))");
            Expr values(read_response());
            Time_const_value t_init = get_value<Time_const_value>(values);
            Time_const_value t_end = get_value<Time_const_value>(values);
            return {t_init, t_end};
        }

        Const_values_entry
            Solver::get_step_entry_values(const Const_ids_entry&
                                              const_ids_entry)
        {
            write_str(
                "(get-value ("s
                + to_string(cconst_ids_entry_dt_const(const_ids_entry))
                + " "
                + to_string(cconst_ids_entry_init_const(const_ids_entry))
                + " "
                + to_string(cconst_ids_entry_param_consts(const_ids_entry))
                + "))"
            );
            Expr values(read_response());
            Dt_const_value dt_ = get_value<Dt_const_value>(values);
            Init_const_value init_ = get_value<Init_const_value>(values);
            Const_values param_values;
            const int size_ = values.size()-2;
            param_values.reserve(size_);
            while (values) {
                param_values.push_back(get_value<Const_value>(values));
            }
            return SMT::make_const_values_entry(dt_, init_,
                                                move(param_values));
        }

        Const_values_entries
            Solver::get_step_entries_values(const Const_ids_entries&
                                                const_ids_entries)
        {
            Const_values_entries entries_values;
            entries_values.reserve(const_ids_entries.size());
            transform(const_ids_entries, std::back_inserter(entries_values),
                      [this](const Const_ids_entry& const_ids_entry){
                          return get_step_entry_values(const_ids_entry);
                      });
            return entries_values;
        }

        Const_values_row
            Solver::get_step_row_values(const Const_ids_row& const_ids_row)
        {
            const Time_const_ids& time_consts =
                SMT::cconst_ids_row_time_consts(const_ids_row);
            Time_const_values time_values =
                get_step_time_values(time_consts);
            const Const_ids_entries& entries_ids =
                SMT::cconst_ids_row_entries(const_ids_row);
            Const_values_entries entries_values =
                get_step_entries_values(entries_ids);
            return make_const_values_row(move(time_values),
                                         move(entries_values));
        }

        template <typename Arg>
        Arg Solver::get_value(Expr& expr)
        {
            return expr.get_expr().next().get_value<Arg>();
        }

        void Solver::assert(Expr_place&& place)
        {
            Expr cmd_expr{Expr_token::new_etoken("assert"),
                          place.move_to_ptr()};
            command(move(cmd_expr));
        }

        void Solver::assert_step_row(const Const_ids_row& const_ids_row,
                                     const Const_values_row& const_values_row,
                                     const Const_values& ode_result)
        {
            if (_assert_step_cnt++ == 0) {
                write_str("(push 1)");
                push_asserts();
            }

            Expr expr = make_assert_step_row_expr(const_ids_row,
                                                  const_values_row);

            last_asserts().emplace_back(expr);
            add_step_ode_result_asserts(const_ids_row, ode_result, expr);

            assert(move(expr));
        }

        void Solver::assert_last_step_row_conflict()
        {
            expect(!asserts_empty() && last_asserts().size() > 0,
                   "No asserts in assertion stack, cannot add conflict.");
            expect(last_asserts() != _prev_last_asserts,
                   "The same conflict has already been asserted! "s
                   + "(There might be an infinite loop.)");

            write_str("(pop 1)");
            _prev_last_asserts = move(last_asserts());
            pop_asserts();

            Expr expr{Expr_token::new_etoken("not"),
                      Expr::new_expr(Expr_token::new_etoken("and"))};
            transform(_prev_last_asserts,
                      std::back_inserter(expr.next().peek_expr()),
                      [](const Expr& e){
                          return e.clone();
                      });
            expr.reset_pos();

            assert(move(expr));
        }

        bool Solver::asserts_empty()
        {
            return asserts_stack().empty();
        }

        void Solver::push_asserts(Asserts asserts)
        {
            asserts_stack().push(move(asserts));
        }

        void Solver::pop_asserts()
        {
            asserts_stack().pop();
        }

        Solver::Asserts& Solver::last_asserts()
        {
            return asserts_stack().top();
        }

        Expr Solver::make_assert_step_row_expr(const Const_ids_row&
                                                   const_ids_row,
                                               const Const_values_row&
                                                   const_values_row)
        {
            const Time_const_ids& time_consts =
                cconst_ids_row_time_consts(const_ids_row);
            const Time_const_values& time_values =
                cconst_values_row_time_values(const_values_row);
            const Const_ids_entries& entries_ids =
                cconst_ids_row_entries(const_ids_row);
            const Const_values_entries& entries_values =
                cconst_values_row_entries(const_values_row);
            const int eids_size = entries_ids.size();
            const int evals_size = entries_values.size();
            expect(eids_size == evals_size,
                   "Size of const. identifiers and their values mismatch: "s
                   + to_string(eids_size) + " != "
                   + to_string(evals_size));
            Expr expr(Expr_token::new_etoken("and"));
            expr.add_new_expr(const_to_assert_expr(move(time_consts.first),
                                                   time_values.first));
            expr.add_new_expr(const_to_assert_expr(move(time_consts.second),
                                                   time_values.second));
            for_each(entries_ids, std::begin(entries_values),
                     [this, &expr](auto& entry_ids, auto& entry_vals){
                         add_step_entry_asserts(entry_ids, entry_vals, expr);
                     });
            return expr;
        }

        void Solver::add_step_entry_asserts(const Const_ids_entry&
                                                const_ids_entry,
                                            const Const_values_entry&
                                                const_values_entry,
                                            Expr& expr)
        {
            const Dt_const_id& dt_const =
                cconst_ids_entry_dt_const(const_ids_entry);
            Dt_const_value dt_value =
                cconst_values_entry_dt_value(const_values_entry);
            expr.add_new_expr(
                const_to_assert_expr(move(dt_const), dt_value)
            );
            const Init_const_id& init_const =
                cconst_ids_entry_init_const(const_ids_entry);
            Init_const_value init_value =
                cconst_values_entry_init_value(const_values_entry);
            expr.add_new_expr(
                const_to_assert_expr(move(init_const), init_value)
            );
            const Const_ids& param_consts =
                cconst_ids_entry_param_consts(const_ids_entry);
            const Const_values& param_values =
                cconst_values_entry_param_values(const_values_entry);
            const int pids_size = param_consts.size();
            const int pvals_size = param_values.size();
            expect(pids_size == pvals_size,
                   "Size of parameter const. identifiers "s
                   + "and their values of '"
                   + to_string(const_ids_entry) + "' entry"
                   + "mismatch: "s
                   + to_string(pids_size) + " != "
                   + to_string(pvals_size));
            for (int i = 0; i < pids_size; i++) {
                expr.add_new_expr(
                    const_to_assert_expr(move(param_consts[i]),
                                         param_values[i])
                );
            }
        }

        void Solver::add_step_ode_result_asserts(const Const_ids_row&
                                                     const_ids_row,
                                                 const Const_values&
                                                     ode_result,
                                                 Expr& expr)
        {
            const Const_ids_entries& entries_ids =
                cconst_ids_row_entries(const_ids_row);
            const int esize = entries_ids.size();
            for (int e = 0; e < esize; e++) {
                const Const_ids_entry& entry_ids = entries_ids[e];
                const Init_const_id& init_const =
                    cconst_ids_entry_init_const(entry_ids);
                Const_value value = round_ode_result(ode_result[e]);
                Const_id int_ode_id = Parser::mod_int_ode_id(init_const);
                Expr assert_expr =
                    const_to_assert_expr(move(int_ode_id), value);
                expr.add_new_expr(move(assert_expr));
            }
        }

        Expr Solver::const_to_assert_expr(Const_id const_id,
                                          Const_value const_value)
        {
            return eplace_to_assert_expr(
                Expr_token::new_etoken(move(const_id)),
                const_value
            );
        }

        Expr Solver::expr_to_assert_expr(Expr expr,
                                         Const_value const_value)
        {
            return eplace_to_assert_expr(
                expr.move_to_ptr(),
                const_value
            );
        }

        Expr Solver::eplace_to_assert_expr(Expr::Expr_place_ptr place_ptr,
                                           Const_value const_value)
        {
            Expr::Expr_place_ptr value_place =
                Expr_value<Const_value>::new_evalue(const_value);
            neg_literal_to_expr(value_place);
            return {Expr_token::new_etoken("="),
                    move(place_ptr),
                    move(value_place)};
        }

        Const_value Solver::round_ode_result(Const_value value)
        {
            return std::floor(value*ode_result_fact+0.5)/ode_result_fact;
        }

        void Solver::fork_solver()
        {
            int in_fds[2];
            expect(pipe(in_fds) == 0,
                   "Opening of input pipe failed.");
            int out_fds[2];
            expect(pipe(out_fds) == 0,
                   "Opening of output pipe failed.");

            pid_t pid = fork();
            expect(pid >= 0,
                   "Forking of SMT solver failed.");

            /// Parent process?
            if (pid != 0) {
                _pid = pid;
                _in_fd = in_fds[0];
                _out_fd = out_fds[1];
                expect(close(in_fds[1]) == 0
                       && close(out_fds[0]) == 0,
                       "Parent process: closing pipe fds failed.");
                return;
            }

            /// Child process
            expect(dup2(STDOUT_FILENO, STDERR_FILENO) != -1,
                   "Child process: redirection of stderr "s
                   + "to stdout failed.");
            expect(dup2(in_fds[1], STDOUT_FILENO) != -1,
                   "Child process: redirection of stdout "s
                   + "to pipe input failed.");
            expect(dup2(out_fds[0], STDIN_FILENO) != -1,
                   "Child process: redirection of stdin "s
                   + "to pipe output failed.");
            expect(close(in_fds[0]) == 0
                   && close(in_fds[1]) == 0
                   && close(out_fds[0]) == 0
                   && close(out_fds[1]) == 0,
                   "Child process: closing pipe fds failed.");

            execlp("z3", "z3", "-smt2", "-in", (char*)NULL);
            // execlp("cvc4", "cvc4", "-L", "smt2", "-i", (char*)NULL);
            throw Error("Child process: execution of SMT solver failed.");
        }

        void Solver::write_str(string str)
        {
            str += '\n';
            const int size_ = str.size();
            ssize_t count = write(_out_fd, str.c_str(), size_);
            expect(count == size_,
                   "Writing to fd failed.");
            _log_ofs << str;
        }

        void Solver::write_expr(Expr expr)
        {
            write_str(to_string(move(expr)));
        }

        string Solver::read_line(string begin)
        {
            string line(move(begin));
            line.reserve(16);
            while (true) {
                char c = read_char();
                if (c == '\n') {
                    return line;
                }
                line += c;
            }
        }

        string Solver::read_expr()
        {
            string str;
            str.reserve(32);
            int cnt = 1;
            while (true) {
                char c = read_char();
                switch (c) {
                default:
                    break;
                case '(':
                    ++cnt;
                    break;
                case ')':
                    if (--cnt == 0) {
                        return str;
                    }
                    break;
                }
                str += c;
            }
        }

        string Solver::read_response()
        {
            char c;
            string str;
            do { c = read_char(); }
            while (isspace(c));
            if (c == '(') return read_expr();
            return read_line(""s + c);
        }

        char Solver::read_char()
        {
            char c;
            expect(read(_in_fd, &c, 1) == 1,
                   "Reading from fd failed.");
            return c;
        }
    }
}
