#include "parser.hpp"

#include <sstream>

#include <iostream>

using std::cerr;
using std::cout;
using std::endl;

namespace SOS {
    Parser::Parser(istream& is)
        : Parser(Expr(preprocess_input(is)))
    { }

    Parser::Parser(const string& input)
        : Parser(Expr(preprocess_input(input)))
    { }

    Parser::Parser(const Expr& expr)
    {
        expect(expr.is_deep(),
               "Non-expression occured at top level.");
        smt_exprs().reserve(expr.size());
        for (auto&& e : expr.transform_to_exprs()) {
            expect(e.cfront()->is_token(),
                   "Expected command expression, got: "s
                   + to_string(e.cto_expr(0)));
            process_expr(forward<Expr>(e));
        }
    }

    string Parser::preprocess_input(string input)
    {
        istringstream iss(move(input));
        return move(preprocess_input(iss));
    }

    string Parser::preprocess_input(istream& is)
    {
        string str("");
        string tmp;
        while (getline(is, tmp, ';')) {
            str += tmp;
            getline(is, tmp);
        }
        return move(str);
    }

    void Parser::process_expr(Expr expr)
    {
        const string& cmd = expr.cto_token(0).ctoken();
        if (cmd == "declare-ode") {
            process_declare_ode(move(expr));
            return;
        }
        if (cmd == "define-dt") {
            process_define_dt(move(expr));
            return;
        }
        if (cmd == "define-ode-step") {
            process_define_ode_step(move(expr));
            return;
        }
        if (cmd == "assert") {
            process_assert(move(expr));
            return;
        }
        add_smt_expr(move(expr));
    }

    void Parser::process_declare_ode(Expr&& expr)
    {
        expect(expr.size() == 4,
               "Expected ODE function name, "s
               + "expression with dt variants "
               + "and expression with parameter keys, got: "
               + to_string(expr));

        expect(expr[1]->is_token(),
               "Expected ODE function name identifier, got: "s
               + to_string(expr.cto_expr(1)));
        const Ode_key& ode_key_ = expr.cto_token(1).ctoken();
        expect(!has_ode_key(ode_key_),
               "ODE function name '"s + ode_key_ + "' "
               + "has already been declared.");

        const Expr& dt_expr = expr.cto_expr(2);
        expect(!expr[2]->is_token() && dt_expr.is_flat(),
               "Expected expression with dt variant name identifiers, got: "s
               + to_string(*expr[2]));
        for (auto&& dkey : dt_expr.transform_to_tokens()) {
            add_dt_key(ode_key_, move(dkey));
        }

        const Expr& keys_expr = expr.cto_expr(3);
        expect(!expr[3]->is_token() && keys_expr.is_flat(),
               "Expected expression with parameter keys identifiers, got: "s
               + to_string(*expr[3]));
        param_keys(ode_key_).reserve(keys_expr.size()+2);
        param_keys(ode_key_).emplace_back(ode_key_);
        Param_keys&& pkeys = keys_expr.transform_to_tokens();
        move(std::begin(pkeys), std::end(pkeys),
             std::back_inserter(param_keys(ode_key_)));
        param_keys(ode_key_).emplace_back("t");
    }

    void Parser::process_define_dt(Expr&& expr)
    {
        expect(expr.size() == 4,
               "Expected dt variant name, "s
               + "expression with parameter keys "
               + "and expression with dt specification, got: "
               + to_string(expr));

        expect(expr[1]->is_token(),
               "Expected dt variant name identifier, got: "s
               + to_string(expr.cto_expr(1)));
        const Dt_key& dt_key_ = expr.cto_token(1).ctoken();
        expect(has_dt_key(dt_key_),
               "dt variant name '"s + dt_key_ + "' "
               + "has not been declared.");

        // !? check keys

        Dt_spec dt_spec_ = expr[3]->is_token()
                         ? Dt_spec("+ 0 "s + expr.cto_token(3).ctoken())
                         : move(expr.cto_expr(3)) ;
        set_dt_spec(dt_key_, move(dt_spec_));

        int dkey_idx = dt_key_idx(dt_key_);
        add_smt_expr({"(define-fun "s + dt_key_
                      + "  () Dt "
                      + to_string(dkey_idx) +")"});
    }

    void Parser::process_define_ode_step(Expr&& expr)
    {
        expect(expr.size() == 2 && expr[1]->is_token(),
               "Expected initial ODE step size, got: "s
               + to_string(expr));
        expect(!_ode_step_set, "ODE step size has already been set.");
        expect(expr.cto_token(1).get_value_check<Time>(_ode_step),
               "ODE step size is invalid: "s
               + to_string(*expr[1]));
        _ode_step_set = true;
    }

    void Parser::process_assert(Expr&& expr)
    {
        // !!!
        add_smt_expr(move(expr));
    }

    void Parser::process_int_ode(Expr&& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant identifier of constant, "
               + "expression with initial values of ODE "
               + "and parameter values, got: "
               + to_string(expr));
        // !!!
        // staci substituovat primo
        //   - zatim je receno ze to musi byt v prikazu assert
        //   -> nemuze to byt v nejake funkci s parametry
        // odsud by mel jit poznat pocet kroku
        // zatim asi jen spolecne casove okamziky pro vsechny ODE
        //   - a navic to zatim ani nebudu kontrolovat
    }

    bool Parser::has_ode_key(const Ode_key& ode_key_) const
    {
        return codes_spec().count(ode_key_) == 1;
    }

    int Parser::ode_key_idx(const Ode_key& ode_key_) const
    {
        const Odes_spec& odes_spec_ = codes_spec();
        const auto& it = odes_spec_.find(ode_key_);
        return std::distance(std::begin(odes_spec_), it);
    }

    const Parser::Ode_spec& Parser::code_spec(const Ode_key& ode_key_) const
    {
        return codes_spec().at(ode_key_).first;
    }

    Parser::Ode_spec& Parser::ode_spec(const Ode_key& ode_key_)
    {
        return odes_spec()[ode_key_].first;
    }

    bool Parser::has_dt_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().count(dt_key_) == 1;
    }

    int Parser::dt_key_idx(const Dt_key& dt_key_) const
    {
        const Ode_key& ode_key_ = code_key(dt_key_);
        const Ode_spec& ode_spec_ = code_spec(ode_key_);
        // const auto& it = code_spec_it(dt_key_);
        const auto& it = ode_spec_.find(dt_key_);
        return std::distance(std::begin(ode_spec_), it);
    }

    const Parser::Ode_key& Parser::code_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().at(dt_key_);
        // return cdt_keys_map().at(dt_key_).first;
    }

    // const Parser::Ode_spec::iterator&
    //     Parser::code_spec_it(const Dt_key& dt_key_) const
    // {
    //     return cdt_keys_map().at(dt_key_).second;
    // }

    const Parser::Param_keys&
        Parser::cparam_keys(const Ode_key& ode_key_) const
    {
        return codes_spec().at(ode_key_).second;
    }

    Parser::Param_keys& Parser::param_keys(const Ode_key& ode_key_)
    {
        return odes_spec()[ode_key_].second;
    }

    void Parser::add_dt_key(const Ode_key& ode_key_, Dt_key dt_key_)
    {
        ode_spec(ode_key_).emplace(dt_key_, Dt_spec());
        // Ode_spec::iterator it;
        // std::tie(it, std::ignore) =
            // ode_spec(ode_key_).emplace(dt_key_, Dt_spec());
        dt_keys_map().emplace(move(dt_key_), ode_key_);
        // dt_keys_map().emplace(move(dt_key_), make_pair(ode_key_, it));
    }

    void Parser::set_dt_spec(const Dt_key& dt_key_, Dt_spec dt_spec_)
    {
        ode_spec(code_key(dt_key_))[dt_key_] = move(dt_spec_);
    }

    void Parser::add_smt_expr(Expr&& expr)
    {
        smt_exprs().emplace_back(move(expr));
    }

    string Parser::smt_input() const
    {
        cerr << to_string(_odes_spec) << endl;
        string str(smt_init_cmds);
        for (const Expr& expr : csmt_exprs()) {
            str += to_string(expr) + "\n";
        }
        return move(str);
    }
}
