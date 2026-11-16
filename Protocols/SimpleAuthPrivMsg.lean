import Leandy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

inductive Nonce
  | Nat: ℕ → Nonce
  | Chan (a b:ℙ): Nonce
  | Sk (a b:ℙ) (n: ℕ): Nonce
deriving DecidableEq, Repr

instance NonceInhabited : Inhabited Nonce where default := .Nat 0

@[aesop (rule_sets := [protocol]) norm]
def Γ : LabelingEnv Unit Nonce := LabelingEnv.from_singles fun
  | .Chan a b => (𝓟 a) ⊔ (𝓟 b)
  | .Sk a b _ => (𝓟 a) ⊔ (𝓟 b)
  | _ => 𝓟ub

@[simp]
lemma Γ_sk (a b : ℙ) (n : ℕ) :
    Γ.Λ {.Sk a b n} = (𝓟 a) ⊔ (𝓟 b) := by
  unfold Γ
  simp

@[simp]
lemma Γ_chan (a b : ℙ) :
    Γ.Λ {.Chan a b} = (𝓟 a) ⊔ (𝓟 b) := by
  unfold Γ
  simp
namespace Event
  variable (a b : ℙ) (na : 𝐵 Unit Nonce)
  abbrev start : Event Unit Nonce := ⟨"start", [!(); na, .princ a, .princ b]⟩
  abbrev done : Event Unit Nonce := ⟨"done", [!(); na, .princ a, .princ b]⟩
end Event

@[aesop (rule_sets := [protocol]) norm]
def event_preds (_ : LabelingEnv Unit Nonce) (e: Event Unit Nonce) (tr : 𝑇 Unit Nonce) : Prop :=
  match e.tag with
  | "start" => ∃ a b n,
                 n ≠ .fail ∧
                 e.content = (Event.start a b n).content
  | "done" => ∃ a b na,
              na ≠ .fail ∧
              e.content = (Event.done a b na).content ∧
              (.Event (.start a b na ) ∈ tr)
  | _ => true

@[simp]
instance instCryptoPreds: Crypto.CryptoPreds Unit Nonce where
  u_sym_enc_pred _ _ m k _ := ∃ a b : ℙ, m = [!(); k, .princ a, .princ b]

inductive State where
  | Init (a b : ℙ) (na : BytesEq.NonFail Unit Nonce)
  | Null
  deriving Inhabited
derive_parsable (Unit, Nonce) for State


@[simp, aesop (rule_sets := [protocol]) norm]
instance instHasValid: Crypto.HasValid Unit Nonce State where
  valid Γ | .Init a b ⟨na, _⟩, tr  =>
            Crypto.valid_bytes Γ na tr ∧ (.Event $ .start a b na) ∈ tr
          | _, _=> True

  valid_monotone Γ := by
     rintro (_|_) tr tr' htr ⟨h₁, h₂⟩
     simp_all [-List.SuffixPreorder]
     · apply_rules[And.intro, Crypto.valid_bytes_monotone, List.IsSuffix.mem]
     · grind

@[simp, aesop (rule_sets := [protocol]) norm]
instance instUserPreds : Crypto.UserPreds Unit Nonce where
  u_state := State
  u_valid_event := event_preds
  u_valid_event_monotone Γ := by
    rintro ⟨tag, content⟩ tr tr' htr h
    simp_all[event_preds]
    grind[List.IsSuffix.mem]

abbrev authentication (tr : 𝑇 Unit Nonce) : Prop :=
  ∀ n a b, (.Event $ .done a b n) ∈ tr → (.Event $ .start a b n) ∈ tr

open BytesEq in
theorem protocol_authentication (h: Crypto.valid_trace Γ tr) : authentication tr := by
  intros rk a₁ b₁ hin
  obtain ⟨a₂, b₂, rk₁, hfail, heq, hev⟩ := Crypto.valid_trace_mem _ _ _ h hin
  grind

@[simp, aesop (rule_sets := [protocol]) norm]
instance : Inhabited (Crypto.UserPreds.u_state Unit Nonce) := ⟨.Null⟩

section protocol

  abbrev sk (k : 𝐵 Unit Nonce) : 𝐵 Unit Nonce := BytesEq.key () .SymEnc k
  def initiator (a b : ℙ) (n : ℕ) : exchange Unit Nonce := λ _ _ _ _ _ ↦
    let nn : 𝐵 Unit Nonce := BytesEq.nonce (.Sk a b n)
    let bn := BytesEq.const (.Nat n)
    let message : 𝐵 Unit Nonce := [!(); bn, nn]
    { message := .fail,
      chan := .Chan a b,
      priv_message := message,
      state := .Init a b ⟨nn, BytesEq.nonce_fail _⟩,
      events := [.Event $ .start a b nn] }

  def responder (a b : ℙ) : exchange Unit Nonce := λ _ _ chanIn privInput _ ↦
    if chanIn = .Chan a b ∧ privInput ≠ .fail then
      match do_parse (privInput.proj_1 ()) as ℕ with
      | some n =>
        let k : 𝐵 Unit Nonce := BytesEq.nonce (.Sk a b n)
        { message := BytesEq.symenc ()
            [!(); k, BytesEq.princ a, BytesEq.princ b] (sk k) }
      | none => default
    else default

  def initiator_check : exchange Unit Nonce := λ _ input _ _ state => Atom.fromOption do
    let .Init sa sb sn := state | return default
    let dec := input.symdec () (sk sn)
    if dec = [!(); (sn : 𝐵 Unit Nonce), BytesEq.princ sa, BytesEq.princ sb] then
      return { events := [.Event $ .done sa sb sn] }
    return default

end protocol

lemma valid_priv_msg_default (tr : 𝑇 Unit Nonce) (chan : Nonce) :
    ∃ l, Crypto.valid_bytes Γ .fail tr ∧
      Crypto.CryptoPreds.priv_send_pred Γ .fail chan tr ∧
      HasLabel Γ tr .fail l ∧ Γ.Λ {chan} ≤[tr] l := by
  exists 𝓟ub;
  simp

theorem valid_initiator (a b : ℙ) (n : ℕ) (tr : 𝑇 Unit Nonce) :
    valid_exchange.alt Γ tr (initiator a b n) := by
  intro_valid_exchange' for initiator with input hi₁ hi₂ state hs₁
  case valid_events =>
    intro ev hev
    simp [] at hev
    subst hev
    simp [event_preds]
    exists a, b, BytesEq.nonce (.Sk a b n)
    simp
  case valid_priv_msg =>
    refine ⟨Γ.Λ {.Sk a b n}, ?_, ?_, ?_, ?_⟩
    · prove_valid_bytes
    · right
      trivial
    · prove_has_label
      simp
    · intro _ _ h
      simp [] at *
      assumption

lemma ciphertext_is_public (a b : ℙ) (k : 𝐵 Unit Nonce) (l : ℓ Unit Nonce)
    (tr : 𝑇 Unit Nonce) (hk : HasLabel Γ tr k l) :
    (BytesEq.symenc () [!(); k, BytesEq.princ a, BytesEq.princ b] (sk k)).is_public Γ tr := by
  refine ⟨𝓟ub, ?_, ?_⟩
  · apply HasLabel.SymEnc
    · aesop_type_system
    · aesop_type_system
    · intro _ _ h
      trivial
  · simp

theorem valid_responder (a b : ℙ) (tr : 𝑇 Unit Nonce) :
    valid_exchange.alt Γ tr (responder a b) := by
  intro_valid_exchange' for responder with input hi₁ hi₂ state hs₁
  case h_1.valid_bytes =>
    apply Crypto.valid_bytes_symenc
    · prove_valid_bytes
    · prove_valid_bytes
    · right
      exact ⟨a, b, rfl⟩
  case h_1.has_label =>
    apply ciphertext_is_public a b _ _ _ (HasLabel.Xor rfl)

theorem valid_initiator_check (tr : 𝑇 Unit Nonce) :
    valid_exchange.alt Γ tr (initiator_check) := by
  intro_valid_exchange' for initiator_check with input hi₁ hi₂ state hs₁ and chanIn privInput hpi
  case h_1.isTrue.valid_events =>
    rename_i _ sa sb sn h
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    simp only [event_preds]
    exact ⟨sa, sb, sn, sn.prop, rfl, hs₁.2⟩
