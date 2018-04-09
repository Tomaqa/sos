#include "sos.hpp"

#include <iostream>

namespace SOS {
    ostream& operator <<(ostream& os, const Error& rhs)
    {
        if (!rhs._printed) {
            os << to_string(rhs);
            rhs._printed = true;
        }
        return os;
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

    string to_string(istream& rhs)
    {
        string str;

        rhs.seekg(0, std::ios::end);
        int size_ = rhs.tellg();
        if (size_ <= 0) size_ = 32;
        str.reserve(size_);
        rhs.seekg(0, std::ios::beg);

        str.assign(std::istreambuf_iterator<char>(rhs),
                   std::istreambuf_iterator<char>());
        return move(str);
    }
}
