#include "util.hpp"

namespace SOS {
    Util::Flag::Value Util::Flag::value_of(bool set_)
    {
        return set_ ? Value::set : Value::unset;
    }
}
