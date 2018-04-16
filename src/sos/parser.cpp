#include "parser.hpp"

#include <sstream>

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
            expect(e.cfront()->is_etoken(),
                   "Expected command expression, got: "s
                   + to_string(e.cto_expr(0)));
            process_expr(forward<Expr>(e));
        }
    }

    const Parser::Ode& Parser::code(const Ode_key& ode_key_) const
    {
        const int idx = code_key_idx(ode_key_);
        return codes()[idx];
    }

    Parser::Ode& Parser::ode(const Ode_key& ode_key_)
    {
        const int idx = code_key_idx(ode_key_);
        return odes()[idx];
    }

    const Parser::Dt_keys& Parser::cdt_keys(const Ode_key& ode_key_) const
    {
        return get<1>(code(ode_key_));
    }

    Parser::Dt_keys& Parser::dt_keys(const Ode_key& ode_key_)
    {
        return get<1>(ode(ode_key_));
    }

    const ODE::Ode_spec& Parser::code_spec(const Ode_key& ode_key_) const
    {
        return get<2>(code(ode_key_));
    }

    ODE::Ode_spec& Parser::ode_spec(const Ode_key& ode_key_)
    {
        return get<2>(ode(ode_key_));
    }

    const ODE::Param_keys&
        Parser::cparam_keys(const Ode_key& ode_key_) const
    {
        return get<1>(codes_map_value(ode_key_));
    }

    ODE::Param_keys& Parser::param_keys(const Ode_key& ode_key_)
    {
        return get<3>(ode(ode_key_));
    }

    const Parser::Const_ids_rows&
        Parser::cconst_ids(const Ode_key& ode_key_) const
    {
        return get<2>(codes_map_value(ode_key_));
    }

    Parser::Const_ids_rows& Parser::const_ids(const Ode_key& ode_key_)
    {
        return get<4>(ode(ode_key_));
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
    try {
        const string& cmd = expr.cto_token(0);
        expect(cmd != "int-ode",
               "Unexpected command '"s + cmd + "' "
               + "at top level.");
        if (cmd == "define-dt") {
            process_define_dt(expr);
            return;
        }
        if (cmd == "define-ode-step") {
            process_define_ode_step(expr);
            return;
        }
        if (cmd == "assert") {
            process_assert(expr);
        }
        add_smt_expr(move(expr));
    }
    catch (const Error& err) {
        throw "At expression\n"s + to_string(expr) + "\n" + err;
    }

    void Parser::declare_ode(const Ode_key& ode_key_, Expr keys_expr)
    {
        if (has_ode_key(ode_key_)) return;

        add_ode_key(ode_key_);

        expect(keys_expr.is_flat(),
               "Expected expression with parameter keys identifiers, got: "s
               + to_string(keys_expr));
        add_param_keys(ode_key_, move(keys_expr));

        add_smt_expr({"(declare-fun "s
                      + int_ode_identifier(ode_key_)
                      + " (Real) Real)"});
    }

    void Parser::process_define_dt(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant name, "
               + "expression with parameter keys "
               + "and expression with dt specification, got: "
               + to_string(expr));

        const Ode_key& ode_key_ = expr.cto_token_check(1);

        const Dt_key& dt_key_ = expr.cto_token_check(2);

        Expr keys_expr = move(expr.cto_expr_check(3));

        Dt_spec dt_spec_ = expr[4]->is_etoken()
                         ? Dt_spec("+ "s + move(expr.to_token(4)))
                         : move(expr.to_expr(4));

        declare_ode(ode_key_, move(keys_expr));

        check_has_not_dt_key(dt_key_);
        add_dt_key(ode_key_, dt_key_);

        // ! check keys

        add_dt_spec(ode_key_, dt_key_, move(dt_spec_));

        int dkey_idx = cdt_key_idx(dt_key_);
        add_smt_expr({"(define-fun "s + dt_key_
                      + " () Dt "
                      + to_string(dkey_idx) +")"});
    }

    void Parser::process_define_ode_step(Expr& expr)
    {
        expect(expr.size() == 2,
               "Expected initial ODE step size, got: "s
               + to_string(expr));
        expect(!_ode_step_set, "ODE step size has already been set.");
        expect(expr.cto_etoken_check(1).get_value_check<Time>(_ode_step),
               "ODE step size is invalid: "s
               + to_string(*expr[1]));
        _ode_step_set = true;
    }

    void Parser::process_assert(Expr& expr)
    {
        expr.for_each_expr([this](Expr& e){
            if (e.cfront()->is_etoken()
                && e.cto_token(0) == "int-ode") {
                process_int_ode(e);
                return;
            }
            process_assert(e);
        });
    }

    void Parser::process_int_ode(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant identifier of constant, "
               + "expression with initial values of ODE "
               + "and parameter values, got: "
               + to_string(expr));

        const Ode_key& ode_key_ = expr.cto_token_check(1);
        check_has_ode_key(ode_key_);

        const Const_id& dt_const = expr.cto_token_check(2);

        const Expr& init_expr = expr.cto_expr_check(3);
        expect(init_expr.size() == 3 && init_expr.is_flat(),
               "Expected initial values of ODE, got: "s
               + to_string(init_expr));
        const Const_id& init_const = init_expr.cto_token(0);
        auto init_t_consts = make_pair(move(init_expr.cto_token(1)),
                                       move(init_expr.cto_token(2)));

        const Expr& param_expr = expr.cto_expr_check(4);
        expect(param_expr.is_flat(),
               "Expected parameter constants, got: "s
               + to_string(param_expr));
        Const_ids param_consts = move(param_expr.transform_to_tokens());

        add_const_ids_row(ode_key_,
                          move(dt_const), move(init_const),
                          move(init_t_consts), move(param_consts));

        expr.to_token(0) += "_" + ode_key_;
        const int steps_ = csteps(ode_key_);
        expr.erase_places(1);
        expr.add_new_etoken(to_string(steps_-1));
    }

    Parser::Const_id Parser::int_ode_identifier(const Ode_key& ode_key_)
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
               + "has not been defined.");
    }

    const Parser::Odes_map::mapped_type&
        Parser::codes_map_item(const Ode_key& ode_key_) const
    {
        return codes_map().at(ode_key_);
    }

    Parser::Odes_map::mapped_type&
        Parser::odes_map_item(const Ode_key& ode_key_)
    {
        return odes_map()[ode_key_];
    }

    const Parser::Odes_map_value&
        Parser::codes_map_value(const Ode_key& ode_key_) const
    {
        return codes_map_item(ode_key_).first;
    }

    Parser::Odes_map_value&
        Parser::odes_map_value(const Ode_key& ode_key_)
    {
        return odes_map_item(ode_key_).first;
    }

    int Parser::code_key_idx(const Ode_key& ode_key_) const
    {
        return codes_map_item(ode_key_).second;
    }

    int& Parser::ode_key_idx(const Ode_key& ode_key_)
    {
        return odes_map_item(ode_key_).second;
    }

    const Parser::Dts_spec_map&
        Parser::cdts_spec_map(const Ode_key& ode_key_) const
    {
        return get<0>(codes_map_value(ode_key_));
    }

    Parser::Dts_spec_map& Parser::dts_spec_map(const Ode_key& ode_key_)
    {
        return get<0>(odes_map_value(ode_key_));
    }

    void Parser::add_ode_key(const Ode_key& ode_key_)
    {
        const int size_ = codes_map().size();
        ode_key_idx(ode_key_) = size_;
        odes().emplace_back(make_tuple(ode_key_, Dt_keys(), Ode_spec(),
                                       Param_keys(), Const_ids_rows()));
    }

    bool Parser::has_dt_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().count(dt_key_) == 1;
    }

    void Parser::check_has_not_dt_key(const Dt_key& dt_key_) const
    {
        expect(!has_dt_key(dt_key_),
               "dt variant name '"s + dt_key_ + "' "
               + "has already been defined.");
    }

    const Parser::Dt_keys_map::mapped_type&
        Parser::cdt_keys_map_item(const Dt_key& dt_key_) const
    {
        return cdt_keys_map().at(dt_key_);
    }

    Parser::Dt_keys_map::mapped_type&
        Parser::dt_keys_map_item(const Dt_key& dt_key_)
    {
        return dt_keys_map()[dt_key_];
    }

    const Parser::Dt_keys_map_value&
        Parser::cdt_keys_map_value(const Dt_key& dt_key_) const
    {
        return cdt_keys_map_item(dt_key_).first;
    }

    Parser::Dt_keys_map_value&
        Parser::dt_keys_map_value(const Dt_key& dt_key_)
    {
        return dt_keys_map_item(dt_key_).first;
    }

    int Parser::cdt_key_idx(const Dt_key& dt_key_) const
    {
        return cdt_keys_map_item(dt_key_).second;
    }

    int& Parser::dt_key_idx(const Dt_key& dt_key_)
    {
        return dt_keys_map_item(dt_key_).second;
    }

    const Parser::Ode_key& Parser::code_key(const Dt_key& dt_key_) const
    {
        return cdt_keys_map_value(dt_key_);
    }

    void Parser::add_dt_key(const Ode_key& ode_key_, Dt_key dt_key_)
    {
        dts_spec_map(ode_key_).emplace(dt_key_, Dt_spec());
        const int dt_idx = cdt_keys(ode_key_).size();
        dt_keys(ode_key_).emplace_back(dt_key_);
        dt_keys_map().emplace(move(dt_key_), make_pair(ode_key_, dt_idx));
    }

    void Parser::add_dt_spec(const Ode_key& ode_key_,
                             const Dt_key& dt_key_, Dt_spec dt_spec_)
    {
        dts_spec_map(ode_key_)[dt_key_] = dt_spec_;
        ode_spec(ode_key_).emplace_back(move(dt_spec_));
    }

    ODE::Param_keys& Parser::param_keys_map(const Ode_key& ode_key_)
    {
        return get<1>(odes_map_value(ode_key_));
    }

    void Parser::add_param_keys(const Ode_key& ode_key_, Expr expr)
    {
        param_keys_map(ode_key_).reserve(expr.size()+2);
        param_keys_map(ode_key_).emplace_back(ode_key_);
        Param_keys pkeys = move(expr.transform_to_tokens());
        move(std::begin(pkeys), std::end(pkeys),
             std::back_inserter(param_keys_map(ode_key_)));
        param_keys_map(ode_key_).emplace_back("t");
        param_keys(ode_key_) = cparam_keys(ode_key_);
    }

    Parser::Const_ids_rows& Parser::const_ids_map(const Ode_key& ode_key_)
    {
        return get<2>(odes_map_value(ode_key_));
    }

    int Parser::csteps(const Ode_key& ode_key_) const
    {
        return cconst_ids(ode_key_).size();
    }

    void Parser::add_const_ids_row(const Ode_key& ode_key_,
                                   Const_id dt_const, Const_id init_const,
                                   pair<Const_id, Const_id> init_t_consts,
                                   Const_ids param_consts)
    {
        auto ids_tup = make_tuple(move(dt_const),
                                  move(init_const),
                                  move(init_t_consts),
                                  move(param_consts) );
        const_ids_map(ode_key_).emplace_back(ids_tup);
        const_ids(ode_key_).emplace_back(move(ids_tup));
    }

    void Parser::add_smt_expr(Expr expr)
    {
        smt_exprs().emplace_back(move(expr));
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
