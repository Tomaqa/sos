namespace SOS {
    template <typename OSolver>
    string Solver<OSolver>::Run::usage() const
    {
        return Util::Run::usage()
               + usage_row('v', "Sets verbose mode")
               + usage_row('q', "Sets quiet mode")
               + "\nSetting output file will enable storing "
               + "trajectories of all ODEs.";
    }

    template <typename OSolver>
    void Solver<OSolver>::Run::do_stuff()
    {
        Solver<OSolver> solver(*_is_ptr);

        if (_verbose) solver.be_verbose();
        else if (_quiet) solver.be_quiet();

        const bool store_traj = !_ofile.empty();
        if (store_traj) {
            solver.set_traject_ofile(_ofile);
        }

        Sat sat = solver.solve();
        if (_verbose) cout << endl;
        cout << sat << endl;

        #ifdef PROFILE
        solver.print_profile();
        #endif //< PROFILE

        if (sat == Sat::unsat) return;

        solver.print_results();

        if (store_traj) {
            string redirect;
            if (!_quiet) {
                cout << endl;
            }
            else {
                redirect = " &>/dev/null";
            }
            system(("tools/plot_traject.sh "s + _ofile + redirect).c_str());
        }
    }

    template <typename OSolver>
    string Solver<OSolver>::Run::getopt_str() const noexcept
    {
        return Util::Run::getopt_str() + "vq";
    }

    template <typename OSolver>
    void Solver<OSolver>::Run::process_opt(char c)
    {
        Util::Run::process_opt(c);
        switch (c) {
        case 'v':
            _verbose = true;
            _quiet = false;
            break;
        case 'q':
            _quiet = true;
            _verbose = false;
            break;
        }
    }
}
