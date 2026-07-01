import Protocols.PaymentChannel.Protocol
import Protocols.PaymentChannel.Proofs.Soundness
import Protocols.PaymentChannel.Proofs.Liveness.Helpers

/-!
# Liveness of the punish protocol

This file contains the two headline liveness theorems of the PaymentChannel
punish protocol. All supporting lemmas live in `Liveness.Helpers`.

* `punish.sound`: a semantic milestone — if the common fund is spent, then either
  a `PostDefended` event appears in `tr'` or both parties are corrupt.
* `punish.eventually_onchain`: the top-level result — under continuous mining and
  miner liveness, a published punishment transaction ends up on the final
  blockchain (matched, by strip equality, to some on-chain transaction).
-/

open Parsing.Parsable Crypto BytesEq HasValidPublic Blockchain UserPreds

set_option maxHeartbeats 1000000

variable [param: ScriptParam]

section Liveness
  variable (tr tr': 𝑇 Unit Nonce)

  /-- Semantic milestone: if the common fund has been spent in `tr`'s blockchain,
  then after `punish_time` blocks of growth (i.e. in `tr'`) either a `PostDefended`
  punishment event has been emitted, or both parties' keys are corrupt. -/
  theorem punish.sound
    (punish_time : ℕ)
    (ps:×× ℙ) (common_fund)
    (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
    (hnouputs: ∀ s, noutputs s ≠ 0)
    (hmined: Blockchain.mined tr)
    (hheight: tr.get_blockchain.height + punish_time ≤ tr'.get_blockchain.height) (hgrow: tr <= tr')
    (hl: Blockchain.Liveness DefenseSelector punish_time tr tr')
    (hv₁: valid_trace Γ tr) (hv₂: tr.get_blockchain.valid (P2WSH Script)) (hcfv)
    (hcf : Blockchain.Pointer.points_to_common_fund ps.vk tr.get_blockchain common_fund hcfv)
    (hspent: common_fund.spent tr.get_blockchain)
    (h_old: ∀ hrk self balance,
      CommonFund.spent_by_hrk (tr.get_blockchain) ps common_fund hv₂ hcfv self hrk balance →
        ∃ rk i, hrk = rk_hash rk ∧
          (.Old {ps, self, common_fund, i, rk, balance} ∈' tr)) :
      (∃ rk tx, .PostDefended common_fund rk tx ∈' tr') ∨
        (TraceEvent.Corrupt ps.a ∈ tr ∧ TraceEvent.Corrupt ps.b ∈ tr) := by
    -- Phase 1: who spent the common fund? Either both parties are corrupt, or an
    -- honest party spent it via a revocation hash `hrk`.
    have hspent_or := CommonFund.exists_spent_by_hrk
      (tr := tr) (ps := ps) (common_fund := common_fund) hv₁ hv₂ hcfv hcf hspent
    cases hspent_or with
    | inr hcorr => exact Or.inr hcorr
    | inl hspent_exists =>
    obtain ⟨hrk, self, balance, hspent_hrk⟩ := hspent_exists
    -- `h_old` turns the on-chain spend into an `.Old` event in `tr`, exposing the
    -- revocation key `rk` and timestamp `i` behind `hrk`.
    obtain ⟨rk, i, hhrk, hold⟩ := h_old hrk self balance hspent_hrk
    have hspent_hash :
        CommonFund.spent_by_hrk (tr.get_blockchain) ps common_fund hv₂ hcfv self (rk_hash rk) balance := by
      simpa [hhrk] using hspent_hrk
    let evs : Evs := .Old {ps, self, common_fund, i, rk, balance}
    let s := evs.get_state tr
    -- Phase 2: from the `.Old` event, recover the protocol state at `i` and, via
    -- `punish_CommonFund_spent_by_hrk_strong_enough`, a complete `pc` plus the
    -- punishable transaction `ptx` whose head we will publish.
    obtain ⟨pc_state, hstate, heq_pc_state, hready_state, hrk_state⟩ :=
      punish.get_state.correct tr hv₁ hold
    obtain ⟨pc, ptx, hpc_old, hready, hrk_pc, hhead, hptr, hptx_outputs⟩ :=
      punish_CommonFund_spent_by_hrk_strong_enough
        (tr := tr) (ps := ps) (common_fund := common_fund)
        (self := self) (rk := rk) (balance := balance) (i := i)
        hv₁ hv₂ hcfv hspent_hash hold
    -- `s` reproduces the fields of the `.Old` event; we only need `common_fund`.
    obtain ⟨_pc_oldv, _hps, _hself, hcf, _hpc_old, _hbal⟩ :=
      punish.get_state.fields tr hv₁ hold
    have hs_common_fund : s.common_fund = common_fund := hcf
    have hhead' : ∃ ptx,
        (punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc).head? = some ptx ∧
        (ptx.mk_ptr s.self.toLocalVout).valid (tr.get_blockchain) := ⟨ptx, hhead, hptr⟩
    let msg : 𝐵 Unit Nonce :=
      serialize (β := WithBlockchain Unit) {blockchain := tr.get_blockchain, msg := ()}
    -- Phase 3: discharge the three `Liveness.Select` duties (the selector fires,
    -- the mined message matches, the state at `i` is `s`), then apply the liveness
    -- hypothesis to extend `tr` into `tr' = l₁ ++ l₂ ++ tr`.
    have hselect : Blockchain.Liveness.Select DefenseSelector
        (punish noutputs outputs) tr
        (Blockchain.get_blockchain_idx tr hmined) i msg (.Std s) := by
      refine ⟨?_, ?_, ?_⟩
      · exact DefenseSelector.intro (tr := tr) (ps := ps) (common_fund := common_fund) (t := i) (rk := rk) noutputs outputs hmined hnouputs hold
      · simpa [msg] using Blockchain.get_blockchain_idx.sound (tr := tr) hmined
      · exact hstate
    obtain ⟨l₁, l₂, htr'⟩ := hl
      (Blockchain.get_blockchain_idx tr hmined) i msg (.Std s) (punish noutputs outputs)
      hgrow hselect hheight
    -- Phase 4: the punish operation emits a `PostDefended` event; transport it from
    -- the local punish trace into `tr'`.
    obtain ⟨tx, htx⟩ := punish_emits_postdefended
      (i := l₁.length + tr.length) (noutputs := noutputs) (outputs := outputs)
      (b := tr.get_blockchain) (s := s) (pc := pc) (rk := rk)
      hpc_old hready hrk_pc hhead'
    refine Or.inl ⟨rk, tx, ?_⟩
    have htx_cf : .PostDefended common_fund rk tx ∈'
        (punish noutputs outputs (l₁.length + tr.length) msg (.Std s)).as_list_including := by
      simpa [hs_common_fund] using htx
    rw [htr']
    simp [Atom.as_list_including] at htx_cf ⊢
    tauto

  lemma punish.sound'
    (punish_time : ℕ)
    (ps:×× ℙ) (common_fund)
    (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
    (hnouputs: ∀ s, noutputs s ≠ 0)
    (hmined: Blockchain.mined tr)
    (hheight: tr.get_blockchain.height + punish_time ≤ tr'.get_blockchain.height) (hgrow: tr <= tr')
    (hl: Blockchain.Liveness DefenseSelector punish_time tr tr')
    (hv₁: valid_trace Γ tr) (hv₂: tr.get_blockchain.valid (P2WSH Script)) (hcfv)
    (hcf : Blockchain.Pointer.points_to_common_fund ps.vk tr.get_blockchain common_fund hcfv)
    (hspent: common_fund.spent tr.get_blockchain)
    (hc: ¬TraceEvent.Corrupt ps.a ∈ tr ∨ ¬TraceEvent.Corrupt ps.b ∈ tr)
    (h_old: ∀ hrk self balance,
      CommonFund.spent_by_hrk (tr.get_blockchain) ps common_fund hv₂ hcfv self hrk balance →
        ∃ rk i, hrk = rk_hash rk ∧
          (.Old {ps, self, common_fund, i, rk, balance} ∈' tr)) :
      ∃ rk tx, .PostDefended common_fund rk tx ∈' tr' := by
      obtain (_|⟨_,_⟩) : (∃ rk tx, .PostDefended common_fund rk tx ∈' tr' ) ∨
        (TraceEvent.Corrupt ps.a ∈ tr ∧ TraceEvent.Corrupt ps.b ∈ tr) := by aapply punish.sound
      · assumption
      · tauto


  /-- Top-level liveness: under continuous mining and miner liveness, if the
  common fund is spent in `tr`, then by `tr_final` a `PostDefended` punishment
  transaction has been published and is matched (by strip equality) to some
  transaction in `tr_final`'s blockchain — either the punishment itself (no
  race) or a competing punishment that won the race. -/
  theorem punish.eventually_onchain
    (tr tr_final : 𝑇 Unit Nonce)
    (ps:×× ℙ) (common_fund)
    (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
    (hnouputs: ∀ s, noutputs s ≠ 0)
    (punish_time miner_time : ℕ)
    (htime_budget : punish_time + miner_time < param.toSelfDelay)
    (hgrow : tr ≤ tr_final)
    (hheight_final : tr.get_blockchain.height + param.toSelfDelay ≤ tr_final.get_blockchain.height)

    (hv₁: valid_trace Γ tr_final) (hv₂: tr_final.get_blockchain.valid (P2WSH Script))
    (hnot_corrupt : TraceEvent.Corrupt ps.a ∉ tr_final ∧ TraceEvent.Corrupt ps.b ∉ tr_final)

    (hcfv)
    (hcf : Blockchain.Pointer.points_to_common_fund ps.vk tr.get_blockchain common_fund hcfv)
    (hspent: common_fund.spent tr.get_blockchain)

    -- punishement liveness
    (hl_punish : ∀ tr tr_punish : 𝑇 Unit Nonce,
      tr <= tr_final → tr_punish <= tr_final → Blockchain.Liveness DefenseSelector punish_time tr tr_punish)
    -- miner liveness
    (hminer : ∀ t tx,
      Blockchain.miner_liveness (P2WSH Script) Blockchain.published_to_miners miner_time tr_final t tx)
    (hmining: continuous_mining tr_final)

    (hno_collision : ∀ (rk : 𝒃) (stx stx' : Blockchain.StripedTransaction Unit Nonce),
      (.Defended rk stx ∈' tr_final) → (.Defended rk stx' ∈' tr_final) → stx' = stx)
    (h_old: ∀  hrk self balance tr' hv₂ hcfv,
      tr' ≤ tr_final →
      CommonFund.spent_by_hrk (tr'.get_blockchain) ps common_fund hv₂ hcfv self hrk balance →
      ∃ rk i, hrk = rk_hash rk ∧
          (.Old {ps, self, common_fund:=common_fund, i, rk, balance} ∈' tr')) :
    ∃ rk tx tx', (.PostDefended common_fund rk tx ∈' tr_final) ∧ tx' ∈ tr_final.get_blockchain
      ∧ (∃ h₁ h₂ h₃ h₄, tx.strip tr_final.get_blockchain 0 h₁ h₂ = tx'.strip tr_final.get_blockchain 0 h₃ h₄) := by
      -- Phase 1: bootstrap validity of `tr` from `tr_final`, then split on who
      -- spent the common fund. The corruption case is impossible: both parties'
      -- keys are uncorrupt in `tr_final`, hence in the suffix `tr`.
      have h_old_hv₂ tr' (htr: tr' ≤ tr): tr'.get_blockchain.valid (P2WSH Script) := by
        aapply Blockchain.valid_antitone; aapply List.get_blockchain_monotone; trans <;> assumption

      have hv_tr : valid_trace Γ tr := Crypto.valid_trace_antitone (Γ := Γ) hgrow hv₁
      have hv₂_tr : tr.get_blockchain.valid (P2WSH Script) := h_old_hv₂ tr (by rfl)
      have hspent_or := CommonFund.exists_spent_by_hrk
        (tr := tr) (ps := ps) common_fund hv_tr hv₂_tr hcfv hcf hspent
      obtain ⟨hnot_corrupta, hnot_corruptb⟩ := hnot_corrupt
      rcases hspent_or with (hspent_exists|⟨_,_⟩)
      case inr =>
        exfalso
        aapply hnot_corrupta
        aapply List.IsSuffix.mem

      -- Phase 2: pick the cheating transaction that spends the common fund, and
      -- use continuous mining to find a mined `tr_cheating` ≥ the trace up to that
      -- transaction (so the punish delay is measured from its height).
      obtain ⟨cheating_tx, hin, hin'⟩ : ∃ tx ∈ tr.get_blockchain, common_fund ∈ tx.input_ptrs := by
        aapply Pointer.spent.of_tx

      have hheight_lt : tr.get_blockchain.height < tr_final.get_blockchain.height := by omega
      let tr_cheating' := tr.get_blockchain_at_tx cheating_tx
      obtain ⟨tr_cheating, htr₀gew, htr₀leq, htr₀mined, htr₀eq⟩:
        ∃ tr₀, tr_cheating' ≤ tr₀ ∧ tr₀ ≤ tr_final ∧ Blockchain.mined tr₀ ∧ tr_cheating'.get_blockchain = tr₀.get_blockchain :=
        by aapply exists_cheating_tr

      -- Phase 3: let `tr_defend` be a mined trace at height
      -- `tr_cheating.height + punish_time`, i.e. just after the punish window.
      let tr_defend' := tr_final.get_tr_of_blockchain_size (tr_cheating.get_blockchain.height + punish_time)
      obtain ⟨tr_defend, htr₃gew, htr₃leq, htr₃mined, htr₃eq⟩ :
        ∃ tr₀, tr_defend' ≤ tr₀ ∧ tr₀ ≤ tr_final ∧ Blockchain.mined tr₀ ∧ tr_defend'.get_blockchain = tr₀.get_blockchain := by
        aapply exists_defending_tr (tr:=tr)

      -- Phase 4: run `punish.sound'_strong` on `(tr_cheating, tr_defend)` to get
      -- the defend transaction `tx_defend`, the cheating parent `ptx_cheat`, and
      -- a witness that a `Defended` event for `tx_defend` exists in `tr_defend`.
      have ⟨rk, tx_defend, ptx_cheat, self_def, balance_def,
          hev, hptx_cheat_mem_ch, htx_ninputs_strong, ⟨htx_input0, htx_input_eq_strong⟩,
          hptx_outputs_strong, hdef_strong⟩
         : sound'_strong_out tr_cheating tr_defend ps common_fund := by
        have hv2_ch : tr_cheating.get_blockchain.valid (P2WSH Script) := by grind
        have hspent_ch : common_fund.spent tr_cheating.get_blockchain := by grind[Blockchain.input_ptrs_mem]
        have hcfv_ch : common_fund.valid tr_cheating.get_blockchain := by
          aapply Blockchain.Pointer.spent_valid (script_t := P2WSH Script)
        have hv_script_tr : tr.get_blockchain.valid Script := by
          apply Restrictions.valid_blockchain
          aapply Crypto.valid_trace_restriction Γ

        aapply punish.sound'_strong (punish_time:=punish_time)
        case hc =>
          left; intro x; aapply hnot_corrupta
          aapply List.IsSuffix.mem
        case hgrow =>
          have hle_def' : tr_cheating ≤ tr_defend' := by
            aapply List.le_get_tr_of_blockchain_size; omega
          trans <;> assumption
        case hheight =>
          have hcheat_height_le_tr : tr_cheating.get_blockchain.height ≤ tr.get_blockchain.height := by
            apply Blockchain.height_monotone; grind
          have htarget_le_final : tr_cheating.get_blockchain.height + punish_time ≤ tr_final.get_blockchain.height := by omega
          have hheight_def' : tr_defend'.get_blockchain.height = tr_cheating.get_blockchain.height + punish_time := by
            aapply List.get_tr_of_blockchain_size.height_leq
          grind
        all_goals try grind[Blockchain.Pointer.points_to_common_fund.semi_antitone]


      -- Phase 5: unfold the `PostDefended` event into the `PostDefendedP`
      -- predicate, exposing the message index `i`, the single-input shape, and
      -- the spend/validity facts the race analysis will consume.
      obtain ⟨hsm, hninputs, hinput_valid,
        ⟨ptr_cheat, hcspendt_cheat, hptr_cheat_txid_pub, hspends⟩,
        ⟨stx, hstx_in, hstx_h0, hstx_hptr, hstx_eq⟩,
        hv⟩
        : event_preds.PostDefendedP tr_defend common_fund rk tx_defend := by
        have := by
          refine valid_trace_mem Γ _ tr_defend ?_ hev
          exact Crypto.valid_trace_antitone (Γ := Γ) htr₃leq hv₁
        simp[valid_trace_event, Parsing.Parsable.sound, u_valid_event] at this
        assumption

      rename 𝕥 => i
      -- Phase 6: build the deadline trace `tr_final₀` (height
      -- `(tr_defend.rtake i).height + miner_time`) and the height/ordering facts
      -- that both race branches consume.
      let tr_final₀ := (tr_final.get_tr_of_blockchain_size $ (tr_defend.rtake i).get_blockchain.height + miner_time)
      have hpub_def : (tr_defend.rtake i) ≤ tr_defend := List.rtake_self tr_defend i
      have hpub_final : (tr_defend.rtake i) ≤ tr_final := le_trans hpub_def htr₃leq
      have hheight_cheat_le_tr : tr_cheating.get_blockchain.height ≤ tr.get_blockchain.height := by
        rw [← htr₀eq]
        exact Blockchain.height_monotone
          (List.get_blockchain_monotone (List.get_blockchain_at_tx_leq tr cheating_tx))
      have htarget_def_le_final : tr_cheating.get_blockchain.height + punish_time ≤ tr_final.get_blockchain.height := by
        omega
      have hdef_height : tr_defend.get_blockchain.height = tr_cheating.get_blockchain.height + punish_time := by
        have hdef' : tr_defend'.get_blockchain.height = tr_cheating.get_blockchain.height + punish_time := by
          dsimp [tr_defend']
          exact List.get_tr_of_blockchain_size.height_leq tr_final
            (tr_cheating.get_blockchain.height + punish_time) htarget_def_le_final
        rw [← htr₃eq]
        exact hdef'
      have hpub_height_le_def : (tr_defend.rtake i).get_blockchain.height ≤ tr_defend.get_blockchain.height := by
        exact Blockchain.height_monotone (List.get_blockchain_monotone hpub_def)
      have hdeadline_height_le_final :
          (tr_defend.rtake i).get_blockchain.height + miner_time ≤ tr_final.get_blockchain.height := by
        rw [hdef_height] at hpub_height_le_def
        have hstrict : tr_cheating.get_blockchain.height + punish_time + miner_time <
            tr_cheating.get_blockchain.height + param.toSelfDelay := by omega
        omega
      have ho₁: (tr_defend.rtake i) ≤ tr_final₀ := by
        exact List.le_get_tr_of_blockchain_size
          (tr := tr_defend.rtake i) (tr' := tr_final)
          (height := (tr_defend.rtake i).get_blockchain.height + miner_time)
          hpub_final (by omega)
      have ho₂: tr_final₀.get_blockchain.height = (tr_defend.rtake i).get_blockchain.height + miner_time := by
        dsimp [tr_final₀]
        exact List.get_tr_of_blockchain_size.height_leq tr_final
          ((tr_defend.rtake i).get_blockchain.height + miner_time) hdeadline_height_le_final

      -- Phase 7: did the defend tx stay spendable at the deadline? If so it goes
      -- on chain (`liveness_no_race`); otherwise a race winner did, and strip
      -- equality identifies it (`liveness_race`).
      by_cases hspend: Transaction.all_input_spendable tr_final₀.get_blockchain tx_defend
      · -- no race
        aapply liveness_no_race
          (tr_final := tr_final)
          (punish_time := punish_time)
          (tr_defend := tr_defend)
      · -- lost the race
        obtain ⟨tx', hin, hpain⟩
          : ∃ tx',  tx' ∈ List.get_blockchain tr_final ∧ (∃ h₁ h₂ h₃ h₄, tx_defend.strip tr_final.get_blockchain 0 h₁ h₂ = tx'.strip tr_final.get_blockchain 0 h₃ h₄) := by
          aapply liveness_race
            (tr_final := tr_final)
            (punish_time := punish_time)
            (tr_cheating := tr_cheating)
            (tr_defend := tr_defend)
        exists rk, tx_defend, tx'
        and_intros
        · aapply List.IsSuffix.mem
        · assumption
        · assumption
end Liveness
