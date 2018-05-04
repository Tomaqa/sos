#pragma once

#include "sos.hpp"
#include "util/run.hpp"
#include "solver.hpp"

namespace SOS {
    template <typename OSolver>
    class Solver<OSolver>::Run : public Util::Run {
    public:
        using Util::Run::Run;

        virtual string usage() const override;
    protected:
        virtual void do_stuff() override;

        virtual string getopt_str() const noexcept override;
        virtual void process_opt(char c) override;
    private:
        bool _verbose{false};
        bool _quiet{false};
    };
}

#include "solver/run.tpp"
