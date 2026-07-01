import Leandy.Generalities.Order
import Leandy.Core.Trace.Types
import Leandy.Macros.Tactics

/--
A label describes when a term is readble by the attacker.

It is an arbitrary property over traces that grows with the traces.
-/
@[aesop [unsafe [cases, constructors]]]
structure Label (α η:Type) [eqα: DecidableEq α] [eqβ: DecidableEq η] [instP: Parameter α] where
  /--
    if `corrupt₀ tr` holds, then this label is readable by the attacker in the
    trace `tr` and all subsequent traces. We say that the label is *corrupted*.
  -/
  corrupt₀ (tr: 𝑇 α η) : Prop
  /-- A label never gets uncorrupted when the trace grows -/
  monotone: Monotone corrupt₀

notation "ℓ" => Label

/-- since it's corrupted IT'S RADIOACTIVE !!!! -/
infix:50 " ☢₀ " => Label.corrupt₀

namespace Label
  variable {α η:Type} [eqα: DecidableEq α] [eqβ: DecidableEq η] [instP: Parameter α]
  @[simp]
  lemma corrupt_of_label₀ (corrupt₀: 𝑇  α η → Prop) (monotone) (tr: 𝑇 α η) :
    {corrupt₀, monotone} ☢₀ tr ↔ corrupt₀ tr := by
      simp_all only

  section aesop
    @[simp]
    lemma corrupt_monotone (l: ℓ α η) (tr tr': 𝑇 α η) (htr: tr <= tr') (h: l ☢₀ tr): l ☢₀ tr' :=
      by aapply l.monotone
  end aesop
end Label
