#include "smt.hpp"

namespace SOS {
    namespace SMT {
        const Dt_const_id&
            cconst_ids_entry_dt_const(const Const_ids_entry&
                                          const_ids_entry)
        {
            return get<0>(const_ids_entry);
        }

        const Init_const_id&
            cconst_ids_entry_init_const(const Const_ids_entry&
                                            const_ids_entry)
        {
            return get<1>(const_ids_entry);
        }

        const Const_ids&
            cconst_ids_entry_param_consts(const Const_ids_entry&
                                              const_ids_entry)
        {
            return get<2>(const_ids_entry);
        }

        Const_ids_entry make_const_ids_entry(Dt_const_id dt_const,
                                             Init_const_id init_const,
                                             Const_ids param_consts)
        {
            return make_tuple(move(dt_const), move(init_const),
                              move(param_consts));
        }

        const Time_const_ids&
            cconst_ids_row_time_consts(const Const_ids_row& const_ids_row_)
        {
            return const_ids_row_.first;
        }

        const Const_ids_entries&
            cconst_ids_row_entries(const Const_ids_row& const_ids_row_)
        {
            return const_ids_row_.second;
        }

        Const_ids_row make_const_ids_row(Time_const_ids time_consts,
                                         Const_ids_entries entries)
        {
            return make_pair(move(time_consts), move(entries));
        }

        Dt_const_value
            cconst_values_entry_dt_value(const Const_values_entry&
                                             const_values_entry)
        {
            return get<0>(const_values_entry);
        }

        Init_const_value
            cconst_values_entry_init_value(const Const_values_entry&
                                               const_values_entry)
        {
            return get<1>(const_values_entry);
        }

        const Const_values&
            cconst_values_entry_param_values(const Const_values_entry&
                                                 const_values_entry)
        {
            return get<2>(const_values_entry);
        }

        Const_values_entry
            make_const_values_entry(Dt_const_value dt_value,
                                    Init_const_value init_value,
                                    Const_values param_values)
        {
            return make_tuple(dt_value, init_value, move(param_values));
        }

        const Time_const_values&
            cconst_values_row_time_values(const Const_values_row&
                                           const_values_row_)
        {
            return const_values_row_.first;
        }

        const Const_values_entries&
            cconst_values_row_entries(const Const_values_row&
                                          const_values_row_)
        {
            return const_values_row_.second;
        }

        Const_values_row make_const_values_row(Time_const_values time_values,
                                               Const_values_entries entries)
        {
            return make_pair(move(time_values), move(entries));
        }

        void neg_literal_to_expr(Expr::Expr_place_ptr& place_ptr)
        {
            Expr_token& etoken = Expr::ptr_to_etoken(place_ptr);
            Token& token = etoken.token();
            if (!(token[0] == '-' && isdigit(token[1]))) return;
            token.erase(0, 1);
            Expr new_expr("-");
            new_expr.add_new_etoken(move(etoken));
            place_ptr = Expr::new_expr(move(new_expr));
        }
    }

    namespace Util {
        string to_string(const SMT::Sat& sat)
        {
            switch (sat) {
            case SMT::Sat::sat: return "sat";
            case SMT::Sat::unsat: return "unsat";
            default: return "unknown";
            }
        }

        ostream& operator <<(ostream& os, const SMT::Sat& sat)
        {
            return (os << to_string(sat));
        }
    }
}
