#include "smt/solver.hpp"
#include "expr/eval.hpp"

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

        template <typename Arg>
        Arg Solver::get_value(Expr& expr)
        {
            return expr.get_expr().next().get_value<Arg>();
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
