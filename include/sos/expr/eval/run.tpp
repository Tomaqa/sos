namespace SOS {
    template <typename Arg>
    void Expr::Eval<Arg>::Run::do_stuff()
    {
        string line;
        cout << std::setprecision(double_precision) << std::fixed;
        while (getline(*_is_ptr, line)) {
            Expr expr(line);
            if (expr.empty()) continue;
            if (expr.size() == 1) {
                cout << expr.get_etoken() << endl;
                continue;
            }

            Expr::Eval<Arg> eval = expr.get_eval<Arg>();
            if (eval.size() == 0) {
                cout << eval() << endl;
                continue;
            }

            int k = 0;
            while (getline(*_is_ptr, line)) {
                if (line.empty()) {
                    if (k) break;
                    continue;
                }
                k++;
                Expr e_values(line);
                Param_values values(e_values.transform_to_args<Arg>());
                cout << eval(move(values)) << endl;
            }
        }
    }
}
