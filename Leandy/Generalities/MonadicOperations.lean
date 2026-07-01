/--
  Dependent version of `guard` .

  It lets one use the fact that the guard was successful for the rest of the
  computation using a similar trick to Fstar's 'squashed' types.
-/
@[always_inline, inline]
def dguard {f : Type → Type v} [Alternative f] (P:Prop) [Decidable P] : f { _x:  Unit // P} :=
  if h : P then pure ⟨(), h⟩ else failure
