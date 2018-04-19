#include "parser.hpp"

#include <sstream>

#include <iostream>

namespace SOS {
    const Parser::Reserved_macro_fs_map Parser::reserved_macro_fs_map{
        {"#def",    &Parser::parse_macro_def},
        {"#define", &Parser::parse_macro_define},
        {"#let",    &Parser::parse_macro_let},
        {"#if",     &Parser::parse_macro_if},
        {"#ite",    &Parser::parse_macro_ite},
        {"#for",    &Parser::parse_macro_for},
    };

    Parser::Parser(istream& is)
        : Parser(Expr(preprocess_input(is)))
    { }

    Parser::Parser(string input)
        : Parser(Expr(preprocess_input(move(input))))
    { }

    //! It requires to have whole input stored in memory,
    //! potentionally inefficient and dangerous
    Parser::Parser(Expr expr)
    {
        preprocess_expr(expr);
        // expect(expr.is_deep(),
               // "Non-expression occured at top level.");
        smt_exprs().reserve(expr.size());
        // for (auto&& e : expr.transform_to_exprs()) {
        expr.for_each_expr([this](auto& e){
            expect(!e.empty(),
                   "Expected command expression, got empty expression.");
            expect(e.cfront()->is_etoken(),
                   "Expected command expression, got: "s
                   + to_string(e.cto_expr(0)));
            parse_expr(e);
        // }
        });
        // preprocess_expr(expr);
        // smt_exprs().reserve(parser_exprs().size());
        // for (auto& e : parser_exprs()) {
        //     expect(!e.empty(),
        //            "Expected command expression, got empty expression.");
        //     expect(e.cfront()->is_etoken(),
        //            "Expected command expression, got: "s
        //            + to_string(e.cto_expr(0)));
        //     parse_expr(e);
        // }
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

    string Parser::preprocess_input(string&& input)
    {
        istringstream iss(move(input));
        return preprocess_input(iss);
    }

    string Parser::preprocess_input(istream& is)
    {
        string str("");
        string tmp;
        while (getline(is, tmp, ';')) {
            str += tmp;
            getline(is, tmp);
        }
        return str;
    }

    void Parser::preprocess_expr(Expr& expr)
    {
        // parser_exprs().reserve(expr.size()*1.2);
        int pos = 0;
        unsigned depth = 0;
        preprocess_nested_expr(expr, pos, depth);
    }

    void Parser::parse_expr(Expr& expr)
    try {
        const Token& cmd = expr.cto_token(0);
        if (cmd == "define-dt") {
            return parse_define_dt(expr);
        }
        if (cmd == "define-ode-step") {
            return parse_define_ode_step(expr);
        }
        if (cmd == "assert") {
            parse_assert(expr);
        }
        expect(cmd != "int-ode",
               "Unexpected command '"s + cmd + "' "
               + "at top level.");
        add_smt_expr(move(expr));
    }
    catch (const Error& err) {
        throw "At expression\n"s + to_string(expr) + "\n" + err;
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
                      + " (Real) Real)"});
    }

    void Parser::parse_define_dt(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant name, "
               + "expression with parameter keys "
               + "and expression with dt specification, got: "
               + to_string(expr));

        Ode_key ode_key_ = move(expr.to_token_check(1));
        Dt_key dt_key_ = move(expr.to_token_check(2));
        Expr keys_expr = move(expr.to_expr_check(3));
        Dt_spec dt_spec_ = expr[4]->is_etoken()
                         ? Dt_spec("+ "s + move(expr.to_token(4)))
                         : move(expr.to_expr(4));

        declare_ode(ode_key_, keys_expr);

        check_has_not_dt_key(dt_key_);
        add_dt_key(ode_key_, dt_key_);

        //! check keys

        add_dt_spec(ode_key_, dt_key_, move(dt_spec_));

        int dkey_idx = cdt_key_idx(dt_key_);
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
        expect(expr.to_etoken_check(1).get_value_check<Time>(_ode_step),
               "ODE step size is invalid: "s
               + to_string(*expr[1]));
        _ode_step_set = true;
    }

    void Parser::parse_assert(Expr& expr)
    {
        expr.for_each_expr([this](Expr& e){
            if (e.cfront()->is_etoken()
                && e.cto_token(0) == "int-ode") {
                return parse_int_ode(e);
            }
            parse_assert(e);
        });
    }

    void Parser::parse_int_ode(Expr& expr)
    {
        expect(expr.size() == 5,
               "Expected ODE function name, "s
               + "dt variant identifier of constant, "
               + "expression with initial values of ODE "
               + "and parameter values, got: "
               + to_string(expr));

        Ode_key& ode_key_ = expr.to_token_check(1);
        check_has_ode_key(ode_key_);

        Const_id& dt_const = expr.to_token_check(2);

        Expr& init_expr = expr.to_expr_check(3);
        expect(init_expr.size() == 3 && init_expr.is_flat(),
               "Expected initial values of ODE, got: "s
               + to_string(init_expr));
        Const_id& init_const = init_expr.to_token(0);
        auto init_t_consts = make_pair(move(init_expr.to_token(1)),
                                       move(init_expr.to_token(2)));

        Expr& param_expr = expr.to_expr_check(4);
        expect(param_expr.is_flat(),
               "Expected parameter constants, got: "s
               + to_string(param_expr));
        Const_ids param_consts = param_expr.transform_to_tokens();

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

    ODE::Param_keys& Parser::param_keys_map(const Ode_key& ode_key_)
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
        return str;
    }

    bool Parser::is_macro_key(const Macro_key& macro_key_)
    {
        return macro_key_[0] == '#';
    }

    bool Parser::is_reserved_macro_key(const Macro_key& macro_key_)
    {
        return reserved_macro_fs_map.includes(macro_key_);
    }

    bool Parser::has_macro_key(const Macro_key& macro_key_) const
    {
        return macros_map().count(macro_key_) == 1;
    }

    void Parser::check_has_not_macro_key(const Macro_key& macro_key_) const
    {
        expect(!has_macro_key(macro_key_),
               "Macro named '"s + macro_key_ + "' "
               + "has already been defined.");
    }

    Parser::Macro& Parser::macro(const Macro_key& macro_key_) const
    {
        return macros_map()[macro_key_];
    }

    Parser::Macro_params&
        Parser::macro_params(const Macro_key& macro_key_) const
    {
        return get<0>(macro(macro_key_));
    }

    Parser::Macro_body& Parser::macro_body(const Macro_key& macro_key_) const
    {
        return get<1>(macro(macro_key_));
    }

    void Parser::add_macro_key(const Macro_key& macro_key_) const
    {
        macro(macro_key_);
    }

    void Parser::add_macro(const Macro_key& macro_key_,
                           Macro_params macro_params_,
                           Macro_body macro_body_) const
    {
        macro(macro_key_) = make_tuple(move(macro_params_),
                                       move(macro_body_));
    }

    void Parser::preprocess_nested_expr(Expr& expr,
                                        int& pos, unsigned depth)
    {
        const int size_ = expr.size();
        const bool is_top = (depth == 0);
        while (pos < size_) {
            if (expr[pos]->is_etoken()) {
                const Macro_key& macro_key_ = expr.cto_token(pos++);
                if (is_macro_key(macro_key_)) {
                    return parse_macro(expr, pos, macro_key_, is_top);
                }
                expect(!is_top,
                       "Unexpected token at top level: '"s
                       + macro_key_);
                continue;
            }
            Expr& subexpr = expr.to_expr(pos++);
            preprocess_nested_expr(subexpr, pos, depth+1);
            // if (is_top) {
                // add_parser_expr(move(subexpr));
            // }
        }
    }

    void Parser::parse_macro(Expr& expr, int& pos,
                             const Macro_key& macro_key_, bool is_top) const
    {
        if (is_top) {
            return parse_top_macro(expr, pos, macro_key_);
        }
        expect(!is_reserved_macro_key(macro_key_),
               "Unexpected nested reserved macro: '"s
               + macro_key_ + "'");
        parse_user_macro(expr, pos, macro_key_);
    }

    void Parser::parse_top_macro(Expr& expr, int& pos,
                                 const Macro_key& macro_key_) const
    {
        if (is_reserved_macro_key(macro_key_)) {
            return parse_reserved_macro(expr, pos, macro_key_);
        }
        parse_user_macro(expr, pos, macro_key_);
    }

    void Parser::parse_reserved_macro(Expr& expr, int& pos,
                                      const Macro_key& macro_key_) const
    {
        reserved_macro_fs_map[macro_key_](this, expr, pos);
    }

    void Parser::parse_user_macro(Expr& expr, int& pos,
                                  const Macro_key& macro_key_) const
    {
        expect(has_macro_key(macro_key_),
               "Macro was not defined: '"s
               + macro_key_ + "'");
    }

    void Parser::parse_macro_def_helper(Expr& expr, int& pos,
                                        bool one_line) const
    {

    }

    void Parser::parse_macro_let(Expr& expr, int& pos) const
    {

    }

    void Parser::parse_macro_if_helper(Expr& expr, int& pos,
                                       bool else_branch) const
    {
        Expr& cond_expr = expr.to_expr_check(pos++);
        if (!parse_arith_exp<int>(cond_expr)) return;
    }

    void Parser::parse_macro_for(Expr& expr, int& pos) const
    {

    }

    template <typename Arg>
    Arg Parser::parse_arith_exp(Expr& expr) const
    {
        return Arg();
    }

    // void Parser::add_parser_expr(Expr expr) const
    // {
    //     std::cout << "* " << expr << std::endl;
    //     parser_exprs().emplace_back(move(expr));
    // }
}
