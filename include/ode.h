#ifndef ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
#define ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430

#include "sos.h"

namespace SOS {
    namespace ODE {
        using Time = double;
        template <typename T>
        using Interval = pair<T,T>;
        using Value = double;
        using State = vector<Value>;
    }
}

#endif // ___SOS_ODE_H_OUDH98ODIHG5GH54GT938HJ3409FG430
