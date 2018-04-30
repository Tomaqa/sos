#include "smt/solver.hpp"
#include "expr/eval.hpp"

#include <iomanip>

#include <sys/wait.h>

namespace SOS {
    namespace SMT {
        Solver::~Solver()
        {
            close(_fd);
            waitpid(_pid, NULL, 0);
            // _thread.join();
        }

        Solver::Solver(string input)
        {
            _ofname = "/tmp/sos_smt_in.tmp";
            _ofs = ofstream(_ofname);

            fork_solver();

            // _thread = thread(&Solver::receiver, this);
            // _thread.detach();

            _ofs << std::setprecision(8) << std::fixed;
            _ofs << move(input) << endl;
        }

        Sat Solver::check_sat()
        {
            _ofs << "(check-sat)" << endl;
            string res = get_line();
            if (res == "sat") return Sat::sat;
            if (res == "unsat") return Sat::unsat;
            expect(res == "unknown",
                   "Unexpected output of SMT solver:\n" + res);
            return Sat::unknown;
        }

        Time_const_values
            Solver::get_step_time_values(const Time_const_ids& time_consts)
        {
            _ofs << "(get-value ("
                 << time_consts.first << " "
                 << time_consts.second
                 << "))" << endl;
            Expr values(get_line());
            Time_const_value t_init = get_value<Time_const_value>(values);
            Time_const_value t_end = get_value<Time_const_value>(values);
            return {t_init, t_end};
        }

        Const_values_entry
            Solver::get_step_entry_values(const Const_ids_entry&
                                              const_ids_entry)
        {
            _ofs << "(get-value ("
                 << cconst_ids_entry_dt_const(const_ids_entry) << " "
                 << cconst_ids_entry_init_const(const_ids_entry) << " "
                 << cconst_ids_entry_param_consts(const_ids_entry)
                 << "))" << endl;
            Expr values(get_line());
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
            _ofs << "(assert " << expr << ")" << endl;
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
                _ofs << "(pop 1)" << endl;
                expr.add_new_etoken_at_pos("not");
                expr = Expr(Expr::new_expr(move(expr)));
            }
            else {
                _ofs << "(push 1)" << endl;
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
            int fds[2];
            expect(pipe(fds) != -1,
                   "Opening of pipe failed.");

            pid_t pid = fork();
            expect(pid != -1,
                   "Forking of SMT solver failed.");

            if (pid != 0) {
                _pid = pid;
                _fd = fds[0];
                close(fds[1]);
                return;
            }

            dup2(fds[1], STDOUT_FILENO);
            close(fds[1]);
            close(fds[0]);
            expect(execlp("z3", "z3", "-smt2", _ofname.c_str(),
                   (char*)NULL) != -1,
                   "Execution of SMT solver failed.");
        }

        // void Solver::receiver()
        // {
        //     char buffer[4096];
        //     while (1) {
        //         ssize_t count = read(_fd, buffer, sizeof(buffer));
        //         if (count == 0) break;
        //         expect(count != -1,
        //                "Reading from fd failed.");
        //         // cout << buffer << endl;
        //     }
        // }

        string Solver::get_line()
        {
            string str;
            str.reserve(32);
            char c;
            while (1) {
                ssize_t count = read(_fd, &c, 1);
                expect(count == 1,
                       "Reading from fd failed.");
                if (c == '\n') return str;
                str += c;
            }
        }
    }
}
