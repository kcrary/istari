# `Symbol`

The symbol type:

    symbol : U 0

Symbol literals are written using a `` sym` `` parsing directive and
a string lexeme.  For example, ``sym`"foo"``.

The only operation on symbols is equality:

    symbol_eqb : symbol -> symbol -> bool

    istrue_symbol_eqb : forall (s t : symbol) . Bool.istrue (symbol_eqb s t) <-> s = t : symbol

