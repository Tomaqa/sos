namespace SOS {
    template <typename Arg>
    bool Expr::has_values() const
    {
        return std::all_of(cbegin(), cend(),
                           bind(&Expr_token::is_value<Arg>,
                                bind(&Expr::cptr_to_token, _1))
                           );
    }

    template <typename Arg>
    Expr::Elems<Arg> Expr::flat_transform() const
    {
        // ! 'is_flat()' is assumed to be true
        expect(has_values<Arg>(), "Elements are not of demanded type.");
        Elems<Arg> elems;
        elems.reserve(size());
        std::transform(cbegin(), cend(),
                       std::back_inserter(elems),
                       bind(&Expr_token::get_value<Arg>,
                            bind(&Expr::cptr_to_token, _1))
                       );
        return move(elems);
    }
}
