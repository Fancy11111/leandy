import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Basic

@[simp]
abbrev timestamp := ℕ
notation "𝕥" => timestamp

@[simp]
def Principal := String
deriving DecidableEq, Repr, LinearOrder
notation "ℙ" => Principal

instance : Inhabited ℙ := ⟨""⟩
