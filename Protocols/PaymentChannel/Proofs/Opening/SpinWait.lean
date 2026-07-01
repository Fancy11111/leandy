import Protocols.PaymentChannel.Protocol
import Protocols.PaymentChannel.Proofs.GeneralLemmas
open Parsing.Parsable Crypto BytesEq HasValidPublic

variable [param: ScriptParam] (tr: 𝑇 Unit Nonce)

namespace opening
  theorem spin_wait_valid :
    valid_exchange.full Γ tr spin_wait := by
    rintro msg newState evs postevs hr input  ⟨hi₁, hi₂⟩ h_input_in state hs₁ hstep
    rw [Atom.Valid_def _ hstep]
    clear hstep
    unfold spin_wait; simp only []
    simple_split; rename Opening => s
    aapply default_state'; rintro ⟨_, b⟩ wbheq; simp only []
    split <;> simp [Atom.Valid]
    · rename_i hin
      constructor <;> try simp_done
      case valid_restrictions => decide_restrictions
      cases hs₁; expose_names
      aapply hready
      · simp
      · aapply Blockchain.txids.mem_monotone
        aapply hr.blockchain_order (γ:=Unit)
    · constructor <;> try simp_done
      case valid_restrictions => decide_restrictions
namespace opening
