-- import Mathlib.Data.List

namespace List

  -- better name
  inductive IsPseudoLex (α:Type) (τ: α → α → Prop) : List α → List α → Prop
  | nil (l) : IsPseudoLex α τ [] l
  | const (t tl hd hd') (hhd: τ hd hd'): IsPseudoLex α τ (hd :: tl) (t ++ hd'::tl)

  variable {α:Type} {τ: α → α → Prop}

end List
