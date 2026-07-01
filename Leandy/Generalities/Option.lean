
namespace Option
  variable {α :Type} (P: α → Prop) (x: Option α)

  inductive NoneOrP (P: α → Prop) : Option α → Prop where
    | none : NoneOrP P none
    | some (x:α) (h: P x): NoneOrP P (some x)

  attribute [simp] NoneOrP.none
  attribute [simp] NoneOrP.some

  @[simp]
  theorem NoneOrP_none : none.NoneOrP P := by constructor

  @[simp]
  theorem NoneOrP_some (x: α) : (some x).NoneOrP P ↔ P x := by
    constructor <;> intro h
    · cases h; assumption
    · apply NoneOrP.some; assumption

  @[simp]
  theorem none_or_P_iff : x.NoneOrP P ↔ (x.isNone ∨ ∃ y, x = some y ∧ P y) := by
    cases x <;> simp

  instance [inst: (x:α) → Decidable (P x)] : Decidable (x.NoneOrP P) :=
    match h:x with
    | none => .isTrue (by constructor)
    | some y => decidable_of_iff'  _ (NoneOrP_some _ y)
end Option
