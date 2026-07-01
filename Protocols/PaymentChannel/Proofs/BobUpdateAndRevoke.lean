import Protocols.PaymentChannel.Protocol
import Protocols.PaymentChannel.Proofs.GeneralLemmas
import Protocols.PaymentChannel.Proofs.Soundness

set_option maxHeartbeats 5000000

open Parsing.Parsable Crypto BytesEq HasValidPublic Blockchain

variable [param: ScriptParam] (tr: 𝑇 Unit Nonce)

/--
  Proof of validity for `bob_update_and_revoke`

  By Gemini & Simon
-/
theorem bob_update_and_revoke_valid : valid_exchange.full Γ tr bob_update_and_revoke := by
  rintro msg newState evs postevs hr input ⟨hv, hip⟩ h_input_in  state hst heq
  rw[Atom.Valid_def _ heq]; clear heq
  unfold bob_update_and_revoke
  aapply default_state'; rintro ⟨msg', b⟩ wbheq; simp only []
  simple_split; rename StdState => s
  aapply default_guard; intro h_cf_valid
  aapply default_guard; intro h_balance_tl
  aapply default_guard; intro hcomplete
  simple_split; rename_i balance srk ohrk osigned i_rk heq
  aapply default_dguard; intro hv_other_ntx
  aapply default_guard; intro h_other_ntx_valid
  aapply default_guard; intro hv_ntx


  -- clean up
  rcases s with ⟨self, ps, common_fund, amount, pc_new, pc_old⟩
  cases heq
  simp only [] at *
  simp only [Atom.Valid]
  rcases hst with ⟨hcfv,hvfpv,ha,hcf,hpc, hpc_old⟩

  have hb:  b ≤ List.get_blockchain tr := @hr.with_blockchain _ _ inferInstance b _ input h_input_in wbheq
  have hv_tr_b := hr.valid_blockchain

  let new_balance := AAndB.mk_as self (balance.sum - msg'.balance_to_sender) msg'.balance_to_sender
  let nrk := nonce (α:=Unit) $ Nonce.mk_Rk self ps (i_rk + 1)
  let nself_rk : 𝒃 := ⟨nrk, by simp [nrk]⟩
  let nhrk : 𝒃 := ⟨hash () nrk, by simp [nrk]⟩
  let ntx := mk_base_transaction ps.vk self.other common_fund new_balance msg'.hrk
  obtain ⟨hvmsg,hvb⟩ : HasValidPublic.is_valid_public
                          (γ:=WithBlockchain MkNewState) Γ { msg := msg', blockchain := b } tr := by
    aapply Parsing.ValidParsable.valid_parse at wbheq <;> try exact inferInstance
    prove_is_valid_public

  have : HasValidPublic.is_valid_public Γ ntx tr := by
    constructor <;> simp only [mk_base_transaction, ntx]
    · intro out hin; simp only [Vec.eq_1, Vec.instMembership, unitParam.eq_1, List.mem_cons,
      List.not_mem_nil, or_false] at hin; cases hin
      and_intros; rotate_left; prove_is_valid_public
      aapply Blockchain.Pointer.valid_is_valid_public
    · aesop_type_system
    · intro out hin;
      cases self <;> simp at hin <;> rcases hin with (hin | hin) <;> cases hin
      all_goals (
        aapply Parsing.ValidParsable.valid_serilaize'
        aapply HasValidPublic.valid_public_hash; right; exact True.intro
        aapply Parsing.ValidParsable.valid_bytes_serialize)
      all_goals constructor <;> (first | exact hvmsg.hrk | exact True.intro | prove_is_valid_public)


  constructor
  case valid_events => simp[UserPreds.u_valid_event]
  case valid_post_events => rintro _ ⟨⟩
  case valid_public_bytes =>
    aapply Parsing.ValidParsable.valid_serialize; constructor
    case revoke =>
      constructor
      cases srk
      have := hpc.self_rk_eq_nonce
      clear * - this
      simp only [] at this; cases this
      aesop_type_system
      rw[<- LabelAt.public_atldef]
      simp[Γ]
    case new_state =>
      constructor
      case balance_to_sender => trivial
      case hrk =>
        prove_is_valid_public
        right; exact True.intro
      case striped_tx_sign =>
        aapply valid_public_sign
        case hkey => prove_valid_bytes
        case ha =>
          aapply is_valid_public_monotone (a:=tr); aapply List.suffix_append
          aapply Parsing.ValidParsable.valid_serialize
          aapply Blockchain.Transaction.strip.valid_public
        case hpred =>
          right
          left
          apply sign_tx_pred_base.intro (b := b) (ps := ps)
            (tx_owner := self.other) (signer := self)
            (signer_rk := nself_rk) (commitment_hrk := msg'.hrk)
            (cf_ptr := common_fund) (cf_ptr_valid := h_cf_valid)
            (balance := new_balance)
          case hkey => cases self <;> rfl
          case def_m => rfl
          case cf_ptr_is_cf => aapply Blockchain.Pointer.points_to_common_fund.semi_antitone
          case cf_funds_eq =>
            rw[Blockchain.get_output_stable (hb:=by assumption), <-ha]
            rw[PcState.Invariant.amout_eq_balance (amount:=amount) (hv:=by assumption)]
            have hsum : amount = balance.sum := by simpa using hpc.amout_eq_balance
            have hle : msg'.balance_to_sender ≤ balance.sum := by simpa [hsum] using h_balance_tl
            have hsum_new : new_balance.sum = balance.sum := by
              dsimp [new_balance]
              cases self <;> simp at hle ⊢ <;> omega
            exact hsum_new.symm
          case hevs =>
            aapply SigningEvents.accept_update
            · aapply List.mem_cons_of_mem; aapply List.mem_cons_self
            · cases self <;> simp[AOrB.other]
  case valid_state =>
    aapply UserPreds.u_state_has_valid.valid_monotone (a:=tr); aapply List.suffix_append
    constructor
    case a.h => exact hcfv
    case a.hvfpv => exact hvfpv
    case a.ha => exact ha
    case a.hcf => exact hcf
    case a.hpc_new =>
      refine PcState.Invariant.Signed
        (other_ntx := mk_base_transaction ps.vk self common_fund new_balance nhrk)
        (ohrk := msg'.hrk) (signed := msg'.striped_tx_sign)
        (i := i_rk + 1) (balance := new_balance)
        (self_rk := nself_rk) ?h1 ?h2 ?h3 ?h4 ?h5 ?h6
      case h1 | h4 => rfl
      case h5 => exact hvmsg.striped_tx_sign
      · aapply Blockchain.Transaction.valid_ptrs_monotone
      · have hcf_b : Blockchain.Pointer.points_to_common_fund ps.vk b common_fund h_cf_valid := by
          aapply Blockchain.Pointer.points_to_common_fund.semi_antitone
        let other_ntx := mk_base_transaction ps.vk self common_fund new_balance nhrk
        let self_sign : 𝒃 := ⟨BytesEq.sign ()
          (serialize (other_ntx.strip b 0
            (by simp [other_ntx, mk_base_transaction])
            (by simpa [other_ntx, mk_base_transaction] using hv_other_ntx)))
          (sk ps[self]), by
            aapply BytesEq.sign_fail'
            · rfl
            · aapply Parsing.NotFailParsable.serialize_not_fail
            · prove_not_fail⟩
        have h_sign_verif := CommonFund.valid_subsumes_signature
          b ps self common_fund new_balance nhrk self_sign msg'.striped_tx_sign
          h_cf_valid hcf_b h_other_ntx_valid
        rw [h_sign_verif]
        congr 1
        aapply Blockchain.Transaction.strip.grows
      · refine PcState.Invariant.RemoteHash (i := i_rk + 1) (balance := new_balance)
          (self_rk := nself_rk) (ohrk := msg'.hrk) ?_ ?_ ?_
        · rfl
        · exact hvmsg.hrk
        · constructor
          · prove_valid_bytes
          · rfl
          · have hsum : amount = balance.sum := by simpa using hpc.amout_eq_balance
            have hle : msg'.balance_to_sender ≤ balance.sum := by simpa [hsum] using h_balance_tl
            have hsum_new : new_balance.sum = balance.sum := by
              dsimp [new_balance]
              cases self <;> simp at hle ⊢ <;> omega
            exact hsum.trans hsum_new.symm
    case a.hpc_old =>
      constructor
      exact hpc
  case valid_restrictions => decide_restrictions
