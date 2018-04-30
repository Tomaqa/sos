#include "parser.hpp"
#include "expr/preprocess.hpp"

#include <sstream>

namespace SOS {
    Parser::Parser(istream& is, bool preprocess_only)
        : Parser(Expr::Preprocess(is).parse(), preprocess_only)
    { }

    Parser::Parser(string input, bool preprocess_only)
        : Parser(Expr::Preprocess(move(input)).parse(), preprocess_only)
    { }

    //! It requires to have whole input stored in memory,
    //! potentionally inefficient and dangerous
    Parser::Parser(Expr expr, bool preprocess_only)
        : _expr(move(expr))
    {
        if (preprocess_only) return;
        parse();
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

    const Parser::Ode_key& Parser::code_ode_key(const Ode& ode_)
    {
        return get<0>(ode_);
    }

    Parser::Ode_key& Parser::ode_ode_key(Ode& ode_)
    {
        return get<0>(ode_);
    }

    const Parser::Dt_keys& Parser::code_dt_keys(const Ode& ode_)
    {
        return get<1>(ode_);
    }

    Parser::Dt_keys& Parser::ode_dt_keys(Ode& ode_)
    {
        return get<1>(ode_);
    }

    const Parser::Ode_spec& Parser::code_ode_spec(const Ode& ode_)
    {
        return get<2>(ode_);
    }

    Parser::Ode_spec& Parser::ode_ode_spec(Ode& ode_)
    {
        return get<2>(ode_);
    }

    const Parser::Param_keys& Parser::code_param_keys(const Ode& ode_)
    {
        return get<3>(ode_);
    }

    Parser::Param_keys& Parser::ode_param_keys(Ode& ode_)
    {
        return get<3>(ode_);
    }

    const Parser::Const_ids_rows& Parser::code_const_ids_rows(const Ode& ode_)
    {
        return get<4>(ode_);
    }

    Parser::Const_ids_rows& Parser::ode_const_ids_rows(Ode& ode_)
    {
        return get<4>(ode_);
    }

    const Parser::Dt_keys& Parser::cdt_keys(const Ode_key& ode_key_) const
    {
        return code_dt_keys(code(ode_key_));
    }

    Parser::Dt_keys& Parser::dt_keys(const Ode_key& ode_key_)
    {
        return ode_dt_keys(ode(ode_key_));
    }

    const Parser::Ode_spec& Parser::code_spec(const Ode_key& ode_key_) const
    {
        return code_ode_spec(code(ode_key_));
    }

    Parser::Ode_spec& Parser::ode_spec(const Ode_key& ode_key_)
    {
        return ode_ode_spec(ode(ode_key_));
    }

    const Parser::Param_keys&
        Parser::cparam_keys(const Ode_key& ode_key_) const
    {
        return get<1>(codes_map_value(ode_key_));
    }

    Parser::Param_keys& Parser::param_keys(const Ode_key& ode_key_)
    {
        return ode_param_keys(ode(ode_key_));
    }

    const Parser::Const_ids_rows&
        Parser::cconst_ids_rows(const Ode_key& ode_key_) const
    {
        return code_const_ids_rows(code(ode_key_));
    }

    Parser::Const_ids_rows& Parser::const_ids_rows(const Ode_key& ode_key_)
    {
        return ode_const_ids_rows(ode(ode_key_));
    }

    const Parser::Const_ids_row&
        Parser::cconst_ids_row(const Ode_key& ode_key_,
                               const Time_const_ids& time_consts) const
    {
        const int idx = ctime_consts_idx(ode_key_, time_consts);
        return cconst_ids_rows(ode_key_)[idx];
    }

    Parser::Const_ids_row&
        Parser::const_ids_row(const Ode_key& ode_key_,
                              const Time_const_ids& time_consts)
    {
        const int idx = ctime_consts_idx(ode_key_, time_consts);
        return const_ids_rows(ode_key_)[idx];
    }

    const Parser::Const_ids_entries&
        Parser::cconst_ids_entries(const Ode_key& ode_key_,
                                   const Time_const_ids& time_consts) const
    {
        return cconst_ids_map_entries(ode_key_, time_consts);
    }

    Parser::Const_ids_entries&
        Parser::const_ids_entries(const Ode_key& ode_key_,
                                  const Time_const_ids& time_consts)
    {
        return const_ids_row(ode_key_, time_consts).second;
    }

    void Parser::parse()
    {
        smt_exprs().reserve(_expr.size());
        while (_expr) {
            Expr& e = _expr.get_expr();
            expect(!e.empty() && !e.cfront()->is_expr(),
                   "Expected command expression, got: "s
                   + to_string(e));
            parse_top_expr(e);
        }
        _expr.reset_pos_to_valid();
    }

    void Parser::parse_top_expr(Expr& expr)
    try {
        const Token& cmd = expr.cpeek_token();
        if (cmd == "set-logic") {
            expr.next();
            return parse_set_logic(expr);
        }
        if (cmd == "define-dt") {
            expr.next();
            return parse_define_dt(expr);
        }
        if (cmd == "define-ode-step") {
            expr.next();
            return parse_define_ode_step(expr);
        }
        expect(cmd != "int-ode",
               "Unexpected command '"s + cmd + "' "
               + "at top level.");
        parse_expr(expr);
        expr.reset_pos_to_valid();
        add_smt_expr(move(expr));
    }
    catch (const Error& err) {
        throw "At expression\n"s + to_string(expr) + "\n" + err;
    }

    void Parser::parse_expr(Expr& expr)
    {
        if (expr.empty()) return;
        maybe_parse_first_token(expr);
        while (expr) {
            if (!expr.cpeek()->is_expr()) {
                parse_token(expr);
                continue;
            }
            Expr& subexpr = expr.get_expr();
            parse_expr(subexpr);
        }
    }

    void Parser::maybe_parse_first_token(Expr& expr)
    {
        if (expr.cpeek()->is_expr()) return;
        const Token& token = expr.cpeek_token();
        expect(token != "set-logic" && token != "define-dt"
               && token != "define-ode-step",
               "Command '"s + token + "' "
               + "must be at top level.");
        if (token == "int-ode") {
            expr.next();
            return parse_int_ode(expr);
        }
        parse_token(expr);
    }

    void Parser::parse_token(Expr& expr)
    {
        SMT::neg_literal_to_expr(expr.get());
    }

    void Parser::parse_set_logic(Expr& expr)
    {
        expect(!_smt_logic_set,
               "SMT logic has already been set.");
        _smt_logic_set = true;
        Token token = expr.get_token_check();
        expect(!expr, "Additional arguments in 'set-logic': "s
               + to_string(expr));
        expect(token == "QF_UFLRA" || token == "QF_UFNRA" || token == "UFLRA",
               "SMT logic is not supported: '"s
               + to_string(token) + "'");
        _smt_logic = move(token);
    }

    void Parser::declare_ode(const Ode_key& ode_key_, Expr& keys_expr)
    {
        if (has_ode_key(ode_key_)) return;

        add_ode_key(ode_key_);

        expect(keys_expr.is_flat(),
               "Expected expression with parameter keys identifiers, got: "s
               + to_string(keys_expr));
        add_param_keys(ode_key_, keys_expr);

        add_smt_expr({"(declare-fun "s
                      + int_ode_identifier(ode_key_)
                      // + " (Real) Real)"});
                      + " (Real Real) Real)"});
    }

    void Parser::parse_define_dt(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant name, "
               + "expression with parameter keys "
               + "and expression with dt specification, got: "
               + to_string(expr));

        Ode_key ode_key_ = move(expr.get_token_check());
        Dt_key dt_key_ = move(expr.get_token_check());
        Expr keys_expr = move(expr.get_expr_check());
        Dt_spec dt_spec_ = expr.cpeek()->is_expr()
                         ? move(expr.get_expr())
                         : Dt_spec("+ "s + move(expr.get_token()));

        declare_ode(ode_key_, keys_expr);

        check_has_not_dt_key(dt_key_);
        add_dt_key(ode_key_, dt_key_);

        //! check keys

        add_dt_spec(ode_key_, dt_key_, move(dt_spec_));

        const int dkey_idx = cdt_key_idx(dt_key_);
        add_smt_expr({"(define-fun "s + dt_key_
                      + " () Dt "
                      + to_string(dkey_idx) +")"});
    }

    void Parser::parse_define_ode_step(Expr& expr)
    {
        expect(expr.size() == 2,
               "Expected initial ODE step size, got: "s
               + to_string(expr));
        expect(!_ode_step_set, "ODE step size has already been set.");
        _ode_step = expr.get_etoken_check().get_value_check<Time>();
        _ode_step_set = true;
    }

    void Parser::parse_int_ode(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant identifier of constant, "
               + "expression with initial values of ODE "
               + "and parameter values, got: "
               + to_string(expr));

        Ode_key ode_key_ = expr.get_token_check();
        check_has_ode_key(ode_key_);

        Const_id dt_const = expr.get_token_check();

        Expr& init_expr = expr.get_expr_check();
        expect(init_expr.size() == 3 && init_expr.is_flat(),
               "Expected initial values of ODE, got: "s
               + to_string(init_expr));
        Init_const_id init_const = move(init_expr.get_token());
        Time_const_id t_init_ = move(init_expr.get_token());
        Time_const_id t_end_ = move(init_expr.get_token());
        Time_const_ids init_t_consts = make_pair(move(t_init_), move(t_end_));

        Expr& param_expr = expr.get_expr_check();
        expect(param_expr.is_flat(),
               "Expected parameter constants, got: "s
               + to_string(param_expr));
        Const_ids param_consts = param_expr.transform_to_tokens();

        add_const_ids_row(ode_key_, move(init_t_consts),
                          move(dt_const), init_const,
                          move(param_consts));

        expr.reset_pos();
        expr.get_token() += "_" + move(ode_key_);
        expr.erase_at_pos();
        expr.next();
        expr.erase_from_pos();
        expr.add_new_etoken(move(init_const));
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

    void Parser::add_ode_key(Ode_key ode_key_)
    {
        const int size_ = codes_map().size();
        ode_key_idx(ode_key_) = size_;
        odes().emplace_back(make_tuple(move(ode_key_), Dt_keys(), Ode_spec(),
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

    void Parser::add_dt_key(Ode_key ode_key_, Dt_key dt_key_)
    {
        dts_spec_map(ode_key_).emplace(dt_key_, Dt_spec());
        const int dt_idx = cdt_keys(ode_key_).size();
        dt_keys(ode_key_).emplace_back(dt_key_);
        dt_keys_map().emplace(move(dt_key_),
                              make_pair(move(ode_key_), dt_idx));
    }

    void Parser::add_dt_spec(const Ode_key& ode_key_,
                             const Dt_key& dt_key_, Dt_spec dt_spec_)
    {
        dts_spec_map(ode_key_)[dt_key_] = dt_spec_;
        ode_spec(ode_key_).emplace_back(move(dt_spec_));
    }

    Parser::Param_keys& Parser::param_keys_map(const Ode_key& ode_key_)
    {
        return get<1>(odes_map_value(ode_key_));
    }

    void Parser::add_param_keys(const Ode_key& ode_key_, Expr& expr)
    {
        param_keys_map(ode_key_).reserve(expr.size()+2);
        param_keys_map(ode_key_).emplace_back(ode_key_);
        Param_keys pkeys = expr.transform_to_tokens();
        move(std::begin(pkeys), std::end(pkeys),
             std::back_inserter(param_keys_map(ode_key_)));
        param_keys_map(ode_key_).emplace_back("t");
        param_keys(ode_key_) = cparam_keys(ode_key_);
    }

    const Parser::Const_ids_map&
        Parser::cconst_ids_map(const Ode_key& ode_key_) const
    {
        return get<2>(codes_map_value(ode_key_));
    }

    Parser::Const_ids_map& Parser::const_ids_map(const Ode_key& ode_key_)
    {
        return get<2>(odes_map_value(ode_key_));
    }

    bool Parser::has_time_consts(const Ode_key& ode_key_,
                                 const Time_const_ids& time_consts) const
    {
        return cconst_ids_map(ode_key_).count(time_consts) == 1;
    }

    const Parser::Const_ids_map::mapped_type&
        Parser::cconst_ids_map_item(const Ode_key& ode_key_,
                                    const Time_const_ids& time_consts) const
    {
        return cconst_ids_map(ode_key_).at(time_consts);
    }

    Parser::Const_ids_map::mapped_type&
        Parser::const_ids_map_item(const Ode_key& ode_key_,
                                   const Time_const_ids& time_consts)
    {
        return const_ids_map(ode_key_)[time_consts];
    }

    const Parser::Const_ids_entries&
        Parser::cconst_ids_map_entries(const Ode_key& ode_key_,
                                       const Time_const_ids& time_consts)
                                       const
    {
        return cconst_ids_map_item(ode_key_, time_consts).first;
    }

    Parser::Const_ids_entries&
        Parser::const_ids_map_entries(const Ode_key& ode_key_,
                                      const Time_const_ids& time_consts)
    {
        return const_ids_map_item(ode_key_, time_consts).first;
    }

    int Parser::ctime_consts_idx(const Ode_key& ode_key_,
                                 const Time_const_ids& time_consts) const
    {
        return cconst_ids_map_item(ode_key_, time_consts).second;
    }

    int& Parser::time_consts_idx(const Ode_key& ode_key_,
                                 const Time_const_ids& time_consts)
    {
        return const_ids_map_item(ode_key_, time_consts).second;
    }

    int Parser::csteps(const Ode_key& ode_key_) const
    {
        return cconst_ids_rows(ode_key_).size();
    }

    void Parser::add_time_consts(const Ode_key& ode_key_,
                                 Time_const_ids time_consts)
    {
        const int size_ = csteps(ode_key_);
        time_consts_idx(ode_key_, time_consts) = size_;
        const_ids_rows(ode_key_).emplace_back(
            SMT::make_const_ids_row(move(time_consts), Const_ids_entries())
        );
    }

    void Parser::add_const_ids_row(const Ode_key& ode_key_,
                                   Time_const_ids time_consts,
                                   Dt_const_id dt_const,
                                   Init_const_id init_const,
                                   Const_ids param_consts)
    {
        if (!has_time_consts(ode_key_, time_consts)) {
            add_time_consts(ode_key_, time_consts);
        }
        Const_ids_entry ids =
            SMT::make_const_ids_entry(move(dt_const),
                                      move(init_const),
                                      move(param_consts));
        const_ids_map_entries(ode_key_, time_consts).emplace_back(ids);
        const_ids_entries(ode_key_, time_consts).emplace_back(move(ids));
    }

    void Parser::add_smt_expr(Expr expr)
    {
        smt_exprs().emplace_back(move(expr));
    }

    string Parser::preprocessed_input() const
    {
        string str("");
        for (auto& eptr : _expr) {
            str += to_string(*eptr) + "\n";
        }
        return str;
    }

    string Parser::csmt_input() const
    {
        string str("");
        str += "(set-logic " + _smt_logic + ")\n";
        str += smt_init_cmds;
        for (const Expr& expr : csmt_exprs()) {
            str += to_string(expr) + "\n";
        }
        return str;
    }
}
