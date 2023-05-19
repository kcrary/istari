open:Symbol
# `Symbol`

The symbol type:

    symbol : type:symbol

Symbol literals are written using a `` sym` `` parsing directive and
a string lexeme.  For example, ``sym`"foo"``.

The only operation on symbols is equality:

    symbol_eqb : type:symbol_eqb

    istrue_symbol_eqb : type:istrue_symbol_eqb

