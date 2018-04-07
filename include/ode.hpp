#pragma once

#include "sos.hpp"

namespace SOS {
    namespace ODE {
        using Time = double;
        using Times = vector<Time>;
        template <typename T> using Interval = pair<T, T>;
        using Real = double;
        using State = vector<Real>;
        using States = vector<State>;
    }
}
