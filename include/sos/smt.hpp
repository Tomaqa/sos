#pragma once

#include "sos.hpp"
#include "expr.hpp"

namespace SOS {
    namespace SMT {
        enum class Sat { sat, unsat, unknown };

        using Token = Expr::Token;
        using Tokens = Expr::Tokens;

        using Const_id = Token;
        using Const_ids = Tokens;
        using Time_const_id = Const_id;
        using Time_const_ids = pair<Time_const_id, Time_const_id>;
        using Dt_const_id = Const_id;
        using Init_const_id = Const_id;
        using Const_ids_entry = tuple<Dt_const_id, Init_const_id, Const_ids>;
        using Const_ids_entries = vector<Const_ids_entry>;
        using Const_ids_row = pair<Time_const_ids, Const_ids_entries>;
        using Const_ids_rows = vector<Const_ids_row>;

        using Const_value = double;
        using Const_values = vector<Const_value>;
        using Time_const_value = Const_value;
        using Time_const_values = pair<Time_const_value, Time_const_value>;
        using Dt_const_value = Const_value;
        using Init_const_value = Const_value;
        using Const_values_entry = tuple<Dt_const_value, Init_const_value,
                                         Const_values>;
        using Const_values_entries = vector<Const_values_entry>;
        using Const_values_row = pair<Time_const_values,
                                      Const_values_entries>;
        using Const_values_rows = vector<Const_values_row>;

        const Dt_const_id&
            cconst_ids_entry_dt_const(const Const_ids_entry&
                                          const_ids_entry);
        const Init_const_id&
            cconst_ids_entry_init_const(const Const_ids_entry&
                                            const_ids_entry);
        const Const_ids&
            cconst_ids_entry_param_consts(const Const_ids_entry&
                                              const_ids_entry);
        Const_ids_entry make_const_ids_entry(Dt_const_id dt_const,
                                             Init_const_id init_const,
                                             Const_ids param_consts);

        const Time_const_ids&
            cconst_ids_row_time_consts(const Const_ids_row& const_ids_row_);
        const Const_ids_entries&
            cconst_ids_row_entries(const Const_ids_row& const_ids_row_);
        Const_ids_row make_const_ids_row(Time_const_ids time_consts,
                                         Const_ids_entries entries);

        Dt_const_value
            cconst_values_entry_dt_value(const Const_values_entry&
                                             const_values_entry);
        Init_const_value
            cconst_values_entry_init_value(const Const_values_entry&
                                               const_values_entry);
        const Const_values&
            cconst_values_entry_param_values(const Const_values_entry&
                                                 const_values_entry);
        Const_values_entry
            make_const_values_entry(Dt_const_value dt_value,
                                    Init_const_value init_value,
                                    Const_values param_values);

        const Time_const_values&
            cconst_values_row_time_values(const Const_values_row&
                                           const_values_row_);
        const Const_values_entries&
            cconst_values_row_entries(const Const_values_row&
                                          const_values_row_);
        Const_values_row make_const_values_row(Time_const_values time_values,
                                               Const_values_entries entries);

        void neg_literal_to_expr(Expr::Expr_place_ptr& place_ptr);
    }
}
