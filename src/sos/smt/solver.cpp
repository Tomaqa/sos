#include "smt/solver.hpp"
#include "expr/eval.hpp"

#include <iomanip>

#include <sys/wait.h>

#include <iostream>

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
              _out_fd(rhs._out_fd)
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
        }

        Solver::Solver(string input)
        {
            fork_solver();
            write_str(move(input));
        }

        Sat Solver::check_sat()
        {
            write_str("(check-sat)");
            string res = read_line();
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
            Expr values(read_expr());
            Time_const_value t_init = get_value<Time_const_value>(values);
            Time_const_value t_end = get_value<Time_const_value>(values);
            return {t_init, t_end};
        }

        Const_values_entry
            Solver::get_step_entry_values(const Const_ids_entry&
                                              const_ids_entry)
        {
            write_str(
                "get-value ("s
                + to_string(cconst_ids_entry_dt_const(const_ids_entry))
                + " "
                + to_string(cconst_ids_entry_init_const(const_ids_entry))
                + " "
                + to_string(cconst_ids_entry_param_consts(const_ids_entry))
                + "))"
            );
            Expr values(read_expr());
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

        void Solver::assert(Expr& expr)
        {
            check_assert_expr(expr);
            write_str("(assert "s + to_string(expr) + ")");
        }

        void Solver::assert_step_row_values(const Const_ids_row&
                                                const_ids_row,
                                            const Const_values_row&
                                                const_values_row,
                                            bool conflict)
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
            for (int e = 0; e < eids_size; e++) {
                auto& entry_ids = entries_ids[e];
                auto& entry_values = entries_values[e];
                const Dt_const_id& dt_const =
                    cconst_ids_entry_dt_const(entry_ids);
                Dt_const_value dt_value =
                    cconst_values_entry_dt_value(entry_values);
                expr.add_new_expr(
                    const_to_assert_expr(move(dt_const), dt_value)
                );
                const Init_const_id& init_const =
                    cconst_ids_entry_init_const(entry_ids);
                Init_const_value init_value =
                    cconst_values_entry_init_value(entry_values);
                expr.add_new_expr(
                    const_to_assert_expr(move(init_const), init_value)
                );
                const Const_ids& param_consts =
                    cconst_ids_entry_param_consts(entry_ids);
                const Const_values& param_values =
                    cconst_values_entry_param_values(entry_values);
                const int pids_size = param_consts.size();
                const int pvals_size = param_values.size();
                expect(pids_size == pvals_size,
                       "Size of parameter const. identifiers "s
                       + "and their values at [" + to_string(e) + "] entry"
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

            expr = Expr(Expr::new_expr(move(expr)));
            if (conflict) {
                write_str("(pop 1)");
                expr.add_new_etoken_at_pos("not");
                expr = Expr(Expr::new_expr(move(expr)));
            }
            else {
                write_str("(push 1)");
                // add int-ode
            }
            assert(expr);
        }

        void Solver::check_assert_expr(Expr& expr)
        {
            expect(expr.size() == 1,
                   "Expected one assertion element, got: "s
                   + to_string(expr));
        }

        Expr Solver::const_to_assert_expr(Const_id const_id,
                                          Const_value const_value)
        {
            return {Expr_token::new_etoken("="),
                    Expr_token::new_etoken(move(const_id)),
                    Expr_value<Const_value>::new_evalue(move(const_value))};
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
            expect(pid != -1,
                   "Forking of SMT solver failed.");

            /// Parent process?
            if (pid != 0) {
                _pid = pid;
                _in_fd = in_fds[0];
                _out_fd = out_fds[1];
                close(in_fds[1]);
                close(out_fds[0]);
                system("sleep 2");
                return;
            }

            /// Child process
            expect(dup2(in_fds[1], STDOUT_FILENO) != -1,
                   "Child process: redirection of stdout "s
                   + "to pipe input failed.");
            expect(dup2(in_fds[1], STDERR_FILENO) != -1,
                   "Child process: redirection of stderr "s
                   + "to pipe input failed.");
            expect(dup2(out_fds[0], STDIN_FILENO) != -1,
                   "Child process: redirection of stdin "s
                   + "to pipe output failed.");
            close(in_fds[0]);
            close(in_fds[1]);
            close(out_fds[0]);
            close(out_fds[1]);
            // expect(execlp("z3", "z3", "-smt2", "-in", (char*)NULL) != -1,
                   // "Child process: execution of SMT solver failed.");
            // expect(execlp("cvc4", "cvc4", "-L", "smt2", "-i",
            //               (char*)NULL) != -1,
            //        "Child process: execution of SMT solver failed.");
            system("z3 -smt2 -in");
            throw Error("SMT solver terminated unexpectedly.");
        }

        void Solver::write_str(string str)
        {
            const int size_ = str.size();
            ssize_t count = write(_out_fd, str.c_str(), size_);
            expect(count == size_,
                   "Writing to fd failed.");
            std::cerr << "<< " << str << " >>" << endl;
        }

        void Solver::write_expr(Expr expr)
        {
            write_str(to_string(move(expr)));
        }

        string Solver::read_line()
        {
            string line;
            line.reserve(32);
            char c;
            while (1) {
                ssize_t count = read(_in_fd, &c, 1);
                expect(count == 1,
                       "Reading from fd failed.");
                if (c == '\n') break;
                std::cerr << c;
                line += c;
            }
            // std::cerr << ">> " << line << endl;
            std::cerr << endl;
            return line;
        }

        Expr Solver::read_expr()
        {
            string str;
            str.reserve(32);
            char c;
            int cnt = 0;
            bool loop = true;
            while (loop) {
                ssize_t count = read(_in_fd, &c, 1);
                expect(count == 1,
                       "Reading from fd failed.");
                std::cerr << c;
                switch (c) {
                default:
                    break;
                case '(':
                    ++cnt;
                    break;
                case ')':
                    expect(cnt > 0,
                           "Unexpected closing brace after '"s
                           + str + "'");
                    // std::cerr << str << endl;
                    if (--cnt == 0) loop = false;
                    break;
                }
                str += c;
            }
            // std::cerr << ">> " << str << " <<" << endl;
            std::cerr << endl;
            return {move(str)};
        }
    }
}
