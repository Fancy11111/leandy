import Leandy.Core

namespace Parsing
  class Parsable (α β: Type) where
    parse: α → Option β
    serialize: β → α
    sound (x:β): parse (serialize x) = some x

  attribute [simp] Parsable.sound
end Parsing

/-- `Parsing.Parsable.parse` with an explicit type -/
notation "do_parse " x " as " γ => Parsing.Parsable.parse (β:=γ) x
