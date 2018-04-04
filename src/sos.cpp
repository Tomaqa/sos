#include "sos.hpp"

namespace SOS {
    ostream& operator <<(ostream& os, const Error& rhs)
    {
        return (os << to_string(rhs));
    }

    Error Error::operator +(const string& rhs) const
    {
        return Error(_msg + rhs);
    }

    Error operator +(const string& lhs, const Error& rhs)
    {
        return Error(lhs + rhs._msg);
    }

    Error& Error::operator +=(const string& rhs)
    {
        _msg += rhs;
        return *this;
    }
}
