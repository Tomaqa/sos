namespace SOS {
    template <typename OSolver>
    void Solver<OSolver>::Run::do_stuff()
    {
        Solver<OSolver> solver(*_is_ptr);

        const bool store_traj = !_ofile.empty();
        if (store_traj) {
            solver.set_traject_ofile(_ofile);
        }

        Sat sat = solver.solve();
        cout << endl << sat << endl;

        if (sat == Sat::unsat) return;

        if (store_traj) {
            cout << endl;
            system(("tools/plot_traject.sh "s + _ofile).c_str());
        }
    }
}
