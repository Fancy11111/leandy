import Protocols.PaymentChannel.Protocol
import Protocols.PaymentChannel.Proofs.GeneralLemmas
open Parsing.Parsable Crypto BytesEq

variable [param: ScriptParam] (tr: 𝑇 Unit Nonce)

/-- Validity for announcing the next local revocation hash. -/
theorem send_revocation_hash_valid : valid_exchange.full Γ tr send_revocation_hash := by
  rintro msg newState evs postevs hr input ⟨hv, hip⟩ h_input_in state hst heq
  rw [Atom.Valid_def _ heq]; clear heq
  unfold send_revocation_hash
  aapply default_state'
  rintro ⟨msg', b⟩ wbheq
  simp only []
  simple_split
  rename StdState => s
  aapply default_guard
  intro hcf_valid
  aapply default_guard
  intro hcomplete
  simple_split
  rename_i old_rk old_hrk old_sig i_rk heq_pc
  simp only [Atom.Valid]
  constructor
  case valid_public_bytes =>
    aapply Parsing.ValidParsable.valid_serialize
    constructor
    case hrk =>
      aapply HasValidPublic.valid_public_hash
      · right; exact True.intro
      · prove_valid_bytes
  case valid_state =>
    simpa using hst
  case valid_events => rintro _ ⟨⟩
  case valid_post_events => rintro _ ⟨⟩
  case valid_restrictions => decide_restrictions
