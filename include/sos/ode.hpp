#pragma once

#include "sos.hpp"
#include "expr.hpp"
#include "expr/eval.hpp"

namespace SOS {
    namespace ODE {
        using Time = double;
        using Times = vector<Time>;
        template <typename T> using Interval = pair<T, T>;
        using Real = double;
        using State = vector<Real>;
        using States = vector<State>;

        using Dt_spec = Expr;
        using Dt_eval = Expr::Eval<Real>;
        using Ode_spec = vector<Dt_spec>;
        using Odes_spec = vector<Ode_spec>;
        using Dt_id = int;
        using Ode_id = int;
        using Dt_ids = vector<Dt_id>;
        using Ode_ids = vector<Ode_id>;
        using Param_key = Dt_eval::Param_key;
        using Param_keys = Dt_eval::Param_keys;
        using Param_keyss = vector<Param_keys>;
        using Spec = pair<Odes_spec, Param_keyss>;
    }
}
