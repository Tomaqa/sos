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
            cout << endl << "Generating plot ..." << endl;
            system(("gnuplot -e \"ifname='"s
                   + _ofile + "'; ofname='"
                   + _ofile + "_plot.svg'\" "
                   + "tools/traject.gp").c_str());
        }
    }
}
