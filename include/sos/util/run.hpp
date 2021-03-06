#pragma once

#include "sos.hpp"
#include "util.hpp"

#include <iostream>
#include <iomanip>
#include <fstream>

#include <unistd.h>

namespace SOS {
    namespace Util {
        using std::cout;
        using std::cerr;
        using std::cin;
        using std::endl;

        class Run {
        public:
            Run(int argc, const char* argv[]);

            int run();

            virtual string usage() const;
        protected:
            using Argv = char* const*;
            template <typename T> using Stream_ptr = T*;

            static string usage_row(char opt, string desc);

            virtual void init();
            virtual void do_stuff()                                        { }

            void getopts();
            virtual string getopt_str() const noexcept;
            virtual void process_opt(char c);
            void set_istream_ptr(istream* std_is_ptr = &cin);
            void set_ostream_ptr(ostream* std_os_ptr = &cout);

            int _argc;
            Argv _argv;

            string _ifile;
            string _ofile;
            ifstream _ifs;
            ofstream _ofs;
            Stream_ptr<istream> _is_ptr;
            Stream_ptr<ostream> _os_ptr;
        };
    }
}
