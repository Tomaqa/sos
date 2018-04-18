#include "util/run.hpp"

extern char *optarg;
extern int optind, optopt;

namespace SOS {
    namespace Util {
        Run::Run(int argc, const char* argv[])
            : _argc(argc), _argv((Argv)argv)
        { }

        int Run::run()
        try {
            init();
            do_stuff();
            return 0;
        }
        catch (const Error& err) {
            cerr << err << endl;
            return 1;
        }

        void Run::init()
        {
            set_file_names();
            set_istream_ptr();
            set_ostream_ptr();
        }

        string Run::usage() const
        {
            return "USAGE: "s + _argv[0] + " [options] [<input_file>]\n"
                   + "Options:"
                   + "\n    -h    Displays this message and exits"
                   + "\n    -i    Sets input file name"
                   + "\n    -o    Sets output file name";
        }

        void Run::set_file_names()
        try {
            int c;
            while ((c = getopt(_argc, _argv, ":hi:o:")) != EOF) {
                switch (c) {
                case 'h':
                    throw Error();
                case 'i':
                    _ifile = optarg;
                    break;
                case 'o':
                    _ofile = optarg;
                    break;
                case ':':
                    throw Error("Option -"s + (char)optopt
                                + " requires operand"
                                + "\n");
                case '?':
                    throw Error("Unrecognized option: -"s + (char)optopt
                                + "\n");
                }
            }
            if (_argc - optind == 1) {
                _ifile = _argv[optind++];
            }
            expect(_argc - optind == 0,
                   "Additional arguments: "s + _argv[optind]
                   + "\n");
        }
        catch (const Error& err) {
            throw err + usage() + "\n";
        }

        void Run::set_istream_ptr(istream* std_is_ptr)
        {
            if (_ifile.empty()) {
                _is_ptr = std_is_ptr;
            }
            else {
                _ifs = ifstream(_ifile);
                _is_ptr = &_ifs;
            }
            expect(_is_ptr->good(), "Input stream error.");
        }

        void Run::set_ostream_ptr(ostream* std_os_ptr)
        {
            if (_ofile.empty()) {
                _os_ptr = std_os_ptr;
            }
            else {
                _ofs = ofstream(_ofile);
                _os_ptr = &_ofs;
            }
            expect(_os_ptr->good(), "Output stream error.");
        }
    }
}
