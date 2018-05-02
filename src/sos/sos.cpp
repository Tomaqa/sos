#include "sos.hpp"

#include <istream>
#include <iomanip>

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

    string to_string(char arg)
    {
        string str;
        str += arg;
        return str;
    }

    string to_string(int arg)
    {
        return std::to_string(arg);
    }

    string to_string(long arg)
    {
        return std::to_string(arg);
    }

    string to_string(unsigned arg)
    {
        return std::to_string(arg);
    }

    string to_string(unsigned long arg)
    {
        return std::to_string(arg);
    }

    string to_string(float arg)
    {
        ostringstream oss;
        oss << std::setprecision(float_precision) << std::fixed << arg;
        return oss.str();
    }

    string to_string(double arg)
    {
        ostringstream oss;
        oss << std::setprecision(double_precision) << std::fixed << arg;
        return oss.str();
    }

    //! This is clumsy and not properly tested
    string to_string(istream& rhs)
    {
        string str;
        int size_ = istream_remain_size(rhs);
        if (size_ <= 0) size_ = 32;
        str.reserve(size_);

        str.assign(std::istreambuf_iterator<char>(rhs),
                   std::istreambuf_iterator<char>());
        return str;
    }

    int istream_remain_size(istream& is)
    {
        streampos pos = is.tellg();
        is.seekg(0, std::ios::end);
        auto size_ = is.tellg() - pos;
        is.seekg(pos);
        return size_;
    }
}
