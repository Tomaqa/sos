#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "parser.hpp"

namespace SOS {
    class Parser::Run : public Util::Run {
    public:
        using Util::Run::Run;
    protected:
        virtual void do_stuff() override;

        virtual string getopt_str() const noexcept override;
        virtual void process_opt(char c) override;
    private:
        bool _preprocess_only{false};
    };
}
