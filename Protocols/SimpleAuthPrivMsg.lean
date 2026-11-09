import Leandy

inductive Nonce
  | Nat: ℕ → Nonce
  | Sk (a b:ℙ): Nonce
  /-- The name of the private channel between `a` and `b`. -/
  | Chan (a b:ℙ): Nonce
deriving DecidableEq, Repr, Inhabited

@[simp, aesop (rule_sets := [protocol]) norm]
def Γ : LabelingEnv Unit Nonce := LabelingEnv.from_singles fun
  | .Sk _ _ => 𝓢ec
  | .Chan _ _ => 𝓢ec
  | _ => 𝓟ub

