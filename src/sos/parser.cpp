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
            // expect(e.cfront()->is_token(),
            expect(e.cfront()->is_etoken(),
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
        // const string& cmd = expr.cto_token(0).ctoken();
        const string& cmd = expr.cto_etoken(0).ctoken();
        expect(cmd != "int-ode",
               "Unexpected command '"s + cmd + "' "
               + "at top level.");
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
            process_assert(expr);
        }
        add_smt_expr(move(expr));
    }

    void Parser::process_declare_ode(Expr&& expr)
    {
        expect(expr.size() == 4
               // && expr[1]->is_token() && !expr[2]->is_token()
               // && !expr[3]->is_token(),
               && expr[1]->is_etoken() && !expr[2]->is_etoken()
               && !expr[3]->is_etoken(),
               "Expected ODE function name, "s
               + "expression with dt variants "
               + "and expression with parameter keys, got: "
               + to_string(expr));

        // const Ode_key& ode_key_ = expr.cto_token(1).ctoken();
        const Ode_key& ode_key_ = expr.cto_etoken(1).ctoken();
        expect(!has_ode_key(ode_key_),
               "ODE function name '"s + ode_key_ + "' "
               + "has already been declared.");

        const Expr& dt_expr = expr.cto_expr(2);
        expect(dt_expr.is_flat(),
               "Expected expression with dt variant name identifiers, got: "s
               + to_string(dt_expr));
        for (auto&& dkey : dt_expr.transform_to_tokens()) {
            add_dt_key(ode_key_, move(dkey));
        }

        const Expr& keys_expr = expr.cto_expr(3);
        expect(keys_expr.is_flat(),
               "Expected expression with parameter keys identifiers, got: "s
               + to_string(keys_expr));
        param_keys(ode_key_).reserve(keys_expr.size()+2);
        param_keys(ode_key_).emplace_back(ode_key_);
        Param_keys&& pkeys = keys_expr.transform_to_tokens();
        move(std::begin(pkeys), std::end(pkeys),
             std::back_inserter(param_keys(ode_key_)));
        param_keys(ode_key_).emplace_back("t");

        add_smt_expr({"(declare-fun "s
                      + int_ode_identifier(ode_key_)
                      + " (Real) Real)"});
    }

    void Parser::process_define_dt(Expr&& expr)
    {
        // expect(expr.size() == 4 && expr[1]->is_token()
        //        && !expr[2]->is_token(),
        expect(expr.size() == 4 && expr[1]->is_etoken()
               && !expr[2]->is_etoken(),
               "Expected dt variant name, "s
               + "expression with parameter keys "
               + "and expression with dt specification, got: "
               + to_string(expr));

        // const Dt_key& dt_key_ = expr.cto_token(1).ctoken();
        const Dt_key& dt_key_ = expr.cto_etoken(1).ctoken();
        check_has_dt_key(dt_key_);

        // !? check keys

        // Dt_spec dt_spec_ = expr[3]->is_token()
        //                  ? Dt_spec("+ 0 "s + expr.cto_token(3).ctoken())
        //                  : move(expr.cto_expr(3)) ;
        Dt_spec dt_spec_ = expr[3]->is_etoken()
                         ? Dt_spec("+ 0 "s + expr.cto_etoken(3).ctoken())
                         : move(expr.cto_expr(3)) ;
        set_dt_spec(dt_key_, move(dt_spec_));

        int dkey_idx = dt_key_idx(dt_key_);
        add_smt_expr({"(define-fun "s + dt_key_
                      + " () Dt "
                      + to_string(dkey_idx) +")"});
    }

    void Parser::process_define_ode_step(Expr&& expr)
    {
        // expect(expr.size() == 2 && expr[1]->is_token(),
        expect(expr.size() == 2 && expr[1]->is_etoken(),
               "Expected initial ODE step size, got: "s
               + to_string(expr));
        expect(!_ode_step_set, "ODE step size has already been set.");
        // expect(expr.cto_token(1).get_value_check<Time>(_ode_step),
        expect(expr.cto_etoken(1).get_value_check<Time>(_ode_step),
               "ODE step size is invalid: "s
               + to_string(*expr[1]));
        _ode_step_set = true;
    }

    void Parser::process_assert(Expr& expr)
    {
        for (auto& eptr : expr) {
            // if (eptr->is_token()) continue;
            if (eptr->is_etoken()) continue;
            Expr& subexpr = Expr::ptr_to_expr(eptr);
            // if (subexpr.cfront()->is_token()
                // && subexpr.cto_token(0).ctoken() == "int-ode") {
            if (subexpr.cfront()->is_etoken()
                && subexpr.cto_etoken(0).ctoken() == "int-ode") {
                process_int_ode(subexpr);
                continue;
            }
            process_assert(subexpr);
        }
    }

    void Parser::process_int_ode(Expr& expr)
    {
        expect(expr.size() == 5
               // && expr[1]->is_token() && expr[2]->is_token()
               // && !expr[3]->is_token() && !expr[4]->is_token(),
               && expr[1]->is_etoken() && expr[2]->is_etoken()
               && !expr[3]->is_etoken() && !expr[4]->is_etoken(),
               "Expected ODE function name, "s
               + "dt variant identifier of constant, "
               + "expression with initial values of ODE "
               + "and parameter values, got: "
               + to_string(expr));

        // Ode_key ode_key_ = expr.cto_token(1).ctoken();
        Ode_key ode_key_ = expr.cto_etoken(1).ctoken();
        check_has_ode_key(ode_key_);

        // Const_id dt_const = expr.cto_token(2).ctoken();
        Const_id dt_const = expr.cto_etoken(2).ctoken();
        // steps(ode_key_)++;

        Expr init_expr = expr.cto_expr(3);
        expect(init_expr.size() == 3 && init_expr.is_flat(),
               "Expected initial values of ODE, got: "s
               + to_string(init_expr));
        // Const_id init_const = move(init_expr.cto_token(0).ctoken());
        // auto init_t_consts = make_pair(init_expr.cto_token(1).ctoken(),
        //                                init_expr.cto_token(2).ctoken());
        Const_id init_const = move(init_expr.cto_etoken(0).ctoken());
        auto init_t_consts = make_pair(init_expr.cto_etoken(1).ctoken(),
                                       init_expr.cto_etoken(2).ctoken());

        Expr param_expr = expr.cto_expr(4);
        expect(param_expr.is_flat(),
               "Expected parameter constants, got: "s
               + to_string(param_expr));
        Param_keys param_consts = move(param_expr.transform_to_tokens());

        // !
        add_const_ids_row(move(dt_const), move(init_const),
                          move(init_t_consts), {});

        expr.places().erase(expr.begin()+1, expr.end());
        // expr.to_token(0).token() += "_" + ode_key_;
        expr.to_etoken(0).token() += "_" + ode_key_;
        const int steps_ = csteps(ode_key_);
        expr.add_new_place(Expr_token(to_string(steps_-1)));
    }

    Expr::Token Parser::int_ode_identifier(const Ode_key& ode_key_)
    {
        return {"int-ode_" + ode_key_};
    }

    bool Parser::has_ode_key(const Ode_key& ode_key_) const
    {
        return codes_map().count(ode_key_) == 1;
    }

    void Parser::check_has_ode_key(const Ode_key& ode_key_) const
    {
        expect(has_ode_key(ode_key_),
               "ODE function name '"s + ode_key_ + "' "
               + "has not been declared.");
    }

    int Parser::ode_key_idx(const Ode_key& ode_key_) const
    {
        const Odes_map& odes_map_ = codes_map();
        const auto& it = odes_map_.find(ode_key_);
        return std::distance(std::begin(odes_map_), it);
    }

    const Parser::Dts_spec_map& Parser::cdts_spec_map(const Ode_key& ode_key_) const
    {
        return get<0>(codes_map().at(ode_key_));
    }

    Parser::Dts_spec_map& Parser::dts_spec_map(const Ode_key& ode_key_)
    {
        return get<0>(odes_map()[ode_key_]);
    }

    bool Parser::has_dt_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().count(dt_key_) == 1;
    }

    void Parser::check_has_dt_key(const Dt_key& dt_key_) const
    {
        expect(has_dt_key(dt_key_),
               "dt variant name '"s + dt_key_ + "' "
               + "has not been declared.");
    }

    int Parser::dt_key_idx(const Dt_key& dt_key_) const
    {
        const Ode_key& ode_key_ = code_key(dt_key_);
        const Dts_spec_map& dts_spec_map_ = cdts_spec_map(ode_key_);
        const auto& it = dts_spec_map_.find(dt_key_);
        return std::distance(std::begin(dts_spec_map_), it);
    }

    const Parser::Ode_key& Parser::code_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().at(dt_key_);
    }

    const Parser::Param_keys&
        Parser::cparam_keys(const Ode_key& ode_key_) const
    {
        return get<1>(codes_map().at(ode_key_));
    }

    Parser::Param_keys& Parser::param_keys(const Ode_key& ode_key_)
    {
        return get<1>(odes_map()[ode_key_]);
    }

    void Parser::add_dt_key(const Ode_key& ode_key_, Dt_key dt_key_)
    {
        dts_spec_map(ode_key_).emplace(dt_key_, Dt_spec());
        dt_keys_map().emplace(move(dt_key_), ode_key_);
    }

    void Parser::set_dt_spec(const Dt_key& dt_key_, Dt_spec dt_spec_)
    {
        dts_spec_map(code_key(dt_key_))[dt_key_] = move(dt_spec_);
    }

    void Parser::add_smt_expr(Expr&& expr)
    {
        smt_exprs().emplace_back(move(expr));
    }

    int Parser::csteps(const Ode_key& ode_key_) const
    {
        // return get<2>(codes_map().at(ode_key_));
        return get<2>(codes_map().at(ode_key_)).size();
    }

    void Parser::add_const_ids_row(Const_id&& dt_const, Const_id&& init_const,
                                   pair<Const_id, Const_id>&& init_t_consts,
                                   vector<Const_id>&& param_consts)
    {
        // !
    }

    string Parser::csmt_input() const
    {
        string str(smt_init_cmds);
        for (const Expr& expr : csmt_exprs()) {
            str += to_string(expr) + "\n";
        }
        return move(str);
    }
}
