namespace SOS {
    template <typename OSolver>
    void Solver<OSolver>::Run::do_stuff()
    {
        Solver<OSolver> solver(*_is_ptr);
        Sat sat = solver.solve();
    }
}
