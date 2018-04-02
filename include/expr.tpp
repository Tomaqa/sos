namespace SOS {
    template <typename Arg>
    Expr::Elems<Arg> Expr::flat_transform() const
    {
        // ! 'is_flat()' is assumed to be true
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