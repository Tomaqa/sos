#ifndef ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
#define ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430

#include "sos.hpp"

namespace SOS {
    namespace ODE {
        using Time = double;
        using Times = vector<Time>;
        template <typename T>
        using Interval = pair<T, T>;
        using Real = double;
        using State = vector<Real>;
        using States = vector<State>;
    }
}

#endif // ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
