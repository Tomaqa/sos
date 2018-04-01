namespace SOS {
    template <typename Arg>
    Expr::Elems<Arg> Expr::flat_transform() const
    {
        Elems<Arg> elems;
        std::transform(cbegin(), cend(),
                       std::begin(elems),
                       bind(&Expr_token::get_value<Arg>,
                            bind(&Expr::cptr_to_token, _1))
                       );
        return move(elems);
    }
}
