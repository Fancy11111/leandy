import Protocols.PaymentChannel.Protocol
import Protocols.PaymentChannel.Proofs.Soundness
-- we may need to import more

open Parsing.Parsable Crypto BytesEq HasValidPublic Blockchain UserPreds

set_option maxHeartbeats 1000000

variable [param: ScriptParam]

section Liveness
  variable (tr tr': 𝑇 Unit Nonce)

  @[simp]
  abbrev Blockchain.mined:=
    .MsgSent (serialize (β:= WithBlockchain Unit) {blockchain:=tr.get_blockchain, msg:=()}) ∈ tr


  abbrev continuous_mining tr:=
    ∀ (tr₁ tr₂ : 𝑇 Unit Nonce), tr₁ <= tr → tr₂ <= tr → tr₁.get_blockchain < tr₂.get_blockchain
      → ∃ (tr₃: 𝑇 Unit Nonce), tr₁ <= tr₃ ∧ tr₃ <= tr₂ ∧ Blockchain.mined tr₃ ∧ tr₁.get_blockchain = tr₃.get_blockchain

  omit param in
  lemma continous_mining.antitone: Antitone continuous_mining := by
    intro tra trb htr h tr₁ tr₂ htr₁ htr₂ hbck
    aapply h <;> trans <;> assumption

  def Blockchain.get_blockchain_idx (_htr: Blockchain.mined tr) : 𝕥 :=
    tr.reverse.idxOf
      (.MsgSent (serialize (β:= WithBlockchain Unit) {blockchain:=tr.get_blockchain, msg:=()}))

  omit param in
  lemma Blockchain.get_blockchain_idx.sound (htr: Blockchain.mined tr):
    tr.IsMessageAt (Blockchain.get_blockchain_idx tr htr) (serialize (β:= WithBlockchain Unit) {blockchain:=tr.get_blockchain, msg:=()}) := by
    let msg : 𝐵 Unit Nonce := serialize (β:= WithBlockchain Unit) {blockchain:=tr.get_blockchain, msg:=()}
    let ev : 𝑇𝐸 Unit Nonce := .MsgSent msg
    have hmem : ev ∈ tr.reverse := by
      simpa [Blockchain.mined, ev, msg] using htr
    have hidx' : tr.reverse.idxOf ev < tr.reverse.length :=
      List.idxOf_lt_length_iff.2 hmem
    have hidx : tr.reverse.idxOf ev < tr.length := by
      simpa using hidx'
    refine Trace.IsMessageAt.intro (tr:=tr) (t:=tr.reverse.idxOf ev) (msg:=msg) hidx ?_
    unfold Trace.get_at
    exact List.getElem_idxOf (a:=ev) hidx'

  private lemma WithBlockchain.serialize_ne_block
      (b : Blockchain Unit Nonce) (u : Unit) (blk : Blockchain.Block Unit Nonce) :
      Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce)
        (serialize (β := WithBlockchain Unit) {blockchain := b, msg := u}) ≠ some blk := by
    intro h
    have h' : @Parsing.Parsable.parse (𝐵 Unit Nonce) (Blockchain.Block Unit Nonce)
        (@Parsing.NotFailParsable.toParsable Unit Nonce (Blockchain.Block Unit Nonce) _ _ _
          (Parsing.mkNotFailParsableDisciminant
            (Blockchain.Block.baseNotFailParsable) (Blockchain.Block.discriminant)))
        (serialize (β := WithBlockchain Unit) {blockchain := b, msg := u}) = some blk := by
      simpa [Blockchain.Block.instNotFailParsable] using h
    have hbdisc := @Parsing.discriminate Unit Nonce _ _ _ inferInstance _
      (Blockchain.Block Unit Nonce) (Blockchain.Block.baseNotFailParsable)
      (Blockchain.Block.discriminant)
      (serialize (β := WithBlockchain Unit) {blockchain := b, msg := u}) blk
      Blockchain.Block.discriminant_public h'
    have hwdisc : BytesEq.proj_1 ParameterDefaultTuple.default_tuple_param
        (serialize (β := WithBlockchain Unit) {blockchain := b, msg := u}) =
          WithBlockchain.discr.val := by
      change BytesEq.proj_1 ParameterDefaultTuple.default_tuple_param
        ((WithBlockchain.instNotFailParsableUnitNonce Unit).serialize {blockchain := b, msg := u}) =
          WithBlockchain.discr.val
      simp only [WithBlockchain.instNotFailParsableUnitNonce,
        Parsing.mkNotFailParsableDisciminant]
      rw [BytesEq.proj_1_tuple (hp := by decide)]
      exact (WithBlockchain.baseParsing Unit).serialize_not_fail {blockchain := b, msg := u}
    rw [hwdisc] at hbdisc
    have hneq : WithBlockchain.discr.val ≠
        (Blockchain.Block.discriminant (α:=Unit) (η:=Nonce)).val := by
      native_decide
    exact hneq hbdisc

  lemma continuous_mining.mined_before_block
      {tr_final tr₀ : 𝑇 Unit Nonce} {m : 𝐵 Unit Nonce}
      {blk : Blockchain.Block Unit Nonce}
      (hcont : continuous_mining tr_final)
      (hv_final : valid_trace Γ tr_final)
      (htr₀ : tr₀ ≤ tr_final)
      (hblock_tr : (.MsgSent m :: tr₀) ≤ tr_final)
      (hparse : Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce) m = some blk)
      (hgrow : tr₀.get_blockchain < (.MsgSent m :: tr₀).get_blockchain) :
      Blockchain.mined tr₀ := by
    obtain ⟨tr₃, h₀₃, h₃block, hmined₃, heq_bc⟩ :=
      hcont tr₀ (.MsgSent m :: tr₀) htr₀ hblock_tr hgrow
    obtain h₃₀ | h₃eq := List.IsSuffix.cons'' tr₃ tr₀ (.MsgSent m) h₃block
    · have hlen : tr₃.length = tr₀.length := by
        exact Nat.le_antisymm (List.IsSuffix.length_le h₃₀) (List.IsSuffix.length_le h₀₃)
      have heq : tr₃ = tr₀ := List.IsSuffix.eq_of_length h₃₀ hlen
      simpa [heq] using hmined₃
    · subst tr₃
      exfalso
      unfold Blockchain.mined at hmined₃
      let wbmsg : 𝐵 Unit Nonce :=
        serialize (β:= WithBlockchain Unit)
          {blockchain := (.MsgSent m :: tr₀).get_blockchain, msg := ()}
      have hmem : .MsgSent wbmsg ∈ (.MsgSent m :: tr₀) := by
        simpa [wbmsg]
          using hmined₃
      have hmem_or : TraceEvent.MsgSent wbmsg = TraceEvent.MsgSent m ∨ TraceEvent.MsgSent wbmsg ∈ tr₀ := by
        simpa using hmem
      cases hmem_or with
      | inl hhead =>
          have hm : wbmsg = m := by
            injection hhead
          have hparse_wb :
              Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce)
                (serialize (β := WithBlockchain Unit)
                  {blockchain := (.MsgSent m :: tr₀).get_blockchain, msg := ()}) = some blk := by
            change Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce) wbmsg = some blk
            rw [hm]
            exact hparse
          exact WithBlockchain.serialize_ne_block _ () blk hparse_wb
      | inr htail =>
          have hv₀ : valid_trace Γ tr₀ := Crypto.valid_trace_antitone (Γ := Γ) htr₀ hv_final
          have hr₀ : Restrictions tr₀ := Crypto.valid_trace_restriction Γ tr₀ hv₀
          have hwb_parse :
              (do_parse wbmsg as WithBlockchain Unit) =
                some {blockchain := (.MsgSent m :: tr₀).get_blockchain, msg := ()} := by
            simp [wbmsg, Parsing.Parsable.sound]
          have hle : (.MsgSent m :: tr₀).get_blockchain ≤ tr₀.get_blockchain :=
            Restrictions.with_blockchain (tr := tr₀) hr₀
              ((.MsgSent m :: tr₀).get_blockchain) () wbmsg htail hwb_parse
          exact hgrow.2 hle

  omit param in
  lemma Blockchain.eq_of_le_height_eq {b b' : Blockchain Unit Nonce}
      (hle : b ≤ b') (hheight : b.height = b'.height) : b = b' := by
    cases b with
    | mk blocks =>
    cases b' with
    | mk blocks' =>
      simp only [Blockchain.height] at hheight
      have hblocks : blocks = blocks' := List.IsPrefix.eq_of_length hle hheight
      simp [hblocks]

  omit param in
  lemma Blockchain.le_of_le_of_le_height {b₁ b₂ b : Blockchain Unit Nonce}
      (h₁ : b₁ ≤ b) (h₂ : b₂ ≤ b) (hheight : b₁.height ≤ b₂.height) :
      b₁ ≤ b₂ := by
    cases b₁ with
    | mk blocks₁ =>
    cases b₂ with
    | mk blocks₂ =>
    cases b with
    | mk blocks =>
      simp only [Blockchain.height, LE.le] at h₁ h₂ hheight ⊢
      have htake₁ : blocks₁ = blocks.take blocks₁.length :=
        List.IsPrefix.take_eq blocks₁ blocks h₁
      have htake₂ : blocks₂ = blocks.take blocks₂.length :=
        List.IsPrefix.take_eq blocks₂ blocks h₂
      rw [htake₁, htake₂]
      apply List.prefix_iff_eq_take.mpr
      simp [List.take_take]
      have h₁len : blocks₁.length ≤ blocks.length := List.IsPrefix.length_le h₁
      rw [Nat.min_eq_left h₁len]
      rw [Nat.min_eq_left]
      exact Nat.le_min.mpr ⟨h₁len, hheight⟩

  omit param in
  lemma exists_next_block_of_height_lt
      {tr tr_final : 𝑇 Unit Nonce}
      (hgrow : tr ≤ tr_final)
      (hheight : tr.get_blockchain.height < tr_final.get_blockchain.height) :
      ∃ tr₀ m blk,
        tr ≤ tr₀ ∧ (.MsgSent m :: tr₀) ≤ tr_final ∧
        tr₀.get_blockchain = tr.get_blockchain ∧
        Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce) m = some blk ∧
        tr₀.get_blockchain < (.MsgSent m :: tr₀).get_blockchain := by
    rcases hgrow with ⟨l, rfl⟩
    induction l with
    | nil => simp at hheight
    | cons hd tl ih =>
        let rest : 𝑇 Unit Nonce := tl ++ tr
        by_cases hrest_gt : tr.get_blockchain.height < rest.get_blockchain.height
        · obtain ⟨tr₀, m, blk, htr₀, hblock, hbc, hparse, hgrow_block⟩ := ih hrest_gt
          exact ⟨tr₀, m, blk, htr₀, le_trans hblock (List.suffix_cons hd rest),
            hbc, hparse, hgrow_block⟩
        · have htr_rest : tr ≤ rest := List.suffix_append tl tr
          have hbc_le : tr.get_blockchain ≤ rest.get_blockchain :=
            List.get_blockchain_monotone htr_rest
          have hheight_le : tr.get_blockchain.height ≤ rest.get_blockchain.height :=
            Blockchain.height_monotone hbc_le
          have hheight_rest : rest.get_blockchain.height = tr.get_blockchain.height := by
            omega
          have hbc_eq : rest.get_blockchain = tr.get_blockchain := by
            symm
            exact Blockchain.eq_of_le_height_eq hbc_le hheight_rest.symm
          have hfull_gt_rest : rest.get_blockchain.height < (hd :: rest).get_blockchain.height := by
            rw [hheight_rest]
            simpa [rest] using hheight
          cases hd with
          | MsgSent m =>
              cases hparse : (Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := Blockchain.Block Unit Nonce) m) with
              | none =>
                  simp [List.get_blockchain, hparse] at hfull_gt_rest
              | some blk =>
                  refine ⟨rest, m, blk, htr_rest, by rfl, hbc_eq, hparse, ?_⟩
                  have hle_block : rest.get_blockchain ≤ (.MsgSent m :: rest).get_blockchain :=
                    List.get_blockchain_monotone (List.suffix_cons (.MsgSent m) rest)
                  exact ⟨hle_block, by
                    intro hrev
                    have hheight_rev := Blockchain.height_monotone hrev
                    omega⟩
          | SetState s =>
              simp [List.get_blockchain] at hfull_gt_rest
          | Event e =>
              simp [List.get_blockchain] at hfull_gt_rest
          | Corrupt p =>
              simp [List.get_blockchain] at hfull_gt_rest
          -- REVIEW: I did not really check if this makes sense but it passed
          | PrivMsgSent n m =>
              simp [List.get_blockchain] at hfull_gt_rest


  inductive DefenseSelector (tr:𝑇 Unit Nonce) : 𝕖xchange → 𝕥 → 𝕥 → Prop where
  | intro {t rk} (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
      (htr: Blockchain.mined tr)
      (hnouputs: ∀ s, noutputs s ≠ 0)
      (hold: .Old {ps, self, common_fund,i:=t, rk, balance} ∈' tr):
        DefenseSelector tr (punish noutputs outputs) (Blockchain.get_blockchain_idx tr htr) t

  def Blockchain.published_to_miners (tr : 𝑇 Unit Nonce)
      (tx : Blockchain.Transaction Unit Nonce) (t : 𝕥) : Prop :=
    tr.IsMessageAt t (serialize (β := ToBlockchain) {tx := tx})

  /-- Race-aware on-chain punishment outcome for a target output: some
  post-defended transaction spending this output is present in the blockchain.
  The transaction may be the one we just published, or a competing punishment
  that won the race. -/
  def Blockchain.PunishmentMinedFor (tr : 𝑇 Unit Nonce)
      (target : Blockchain.Pointer Unit Nonce) : Prop :=
    ∃ common_fund rk tx, (.PostDefended common_fund rk tx ∈' tr) ∧
      tx ∈ tr.get_blockchain ∧ tx.spends target

  /-- The `ToLocal` output of a revoked/cheating commitment transaction spending
  `common_fund`.  This packages the existential transaction hidden in
  `CommonFund.spent_by_hrk` together with the output that punishments race to
  spend. -/
  def CommonFund.punishment_target
      (b : Blockchain Unit Nonce) (ps : ×× ℙ)
      (common_fund : Blockchain.Pointer Unit Nonce)
      (hv₂ : b.valid (P2WSH Script)) (hcfv : common_fund.valid b)
      (self : AOrB) (rk : 𝒃) (balance : ×× €)
      (target : Blockchain.Pointer Unit Nonce) : Prop :=
    ∃ ptx, ∃ (hin : ptx ∈ b), ptx.spends common_fund ∧
      (∃ (i : ℕ) (hi : i < ptx.ninputs),
        ptx.strip b i hi
            (by aapply Blockchain.Transaction.strip_valid_ptr (script_t := P2WSH Script)) =
          (mk_base_transaction ps.vk self common_fund balance
            ⟨BytesEq.hash () rk.val, by cases rk; prove_not_fail⟩).strip b 0
              (by simp [mk_base_transaction]) hcfv) ∧
      target = ptx.mk_ptr self.toLocalVout

  omit param in
  lemma Blockchain.Pointer.spendable_of_valid_not_spent
      {b : Blockchain Unit Nonce} {ptr : Blockchain.Pointer Unit Nonce}
      (hptr : ptr.valid b) (hunique : ptr.txid.unique b)
      (hnot_spent : ptr ∉ b.input_ptrs) :
      ptr ∈ b.spendable_ptrs := by
    simp only [Blockchain.spendable_ptrs, Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset]
    constructor
    · constructor
      · rw [Blockchain.output_ptrs_is_valid_ptrs]
        exact hptr
        exact hunique
      · exact hunique
    · exact hnot_spent

  set_option linter.unusedSectionVars false in
  /-- Contrapositive of `spendable_of_valid_not_spent`: a valid, unique pointer
  that is not spendable must already be spent. -/
  lemma Blockchain.Pointer.spent_of_valid_unique_not_spendable
      {b : Blockchain Unit Nonce} {ptr : Blockchain.Pointer Unit Nonce}
      (hptr : ptr.valid b) (hunique : ptr.txid.unique b)
      (hnot_spendable : ptr ∉ b.spendable_ptrs) :
      ptr ∈ b.input_ptrs := by
    by_contra hnot
    exact hnot_spendable (Blockchain.Pointer.spendable_of_valid_not_spent hptr hunique hnot)

  set_option linter.unusedSectionVars false in
  /-- `ptr ∈ b.spendable_ptrs` iff it is not already an input pointer of `b`.
  (The `valid` / `unique` sides are folded into the spendable set definition.) -/
  lemma Blockchain.Pointer.not_spent_of_mem_spendable_ptrs
      {b : Blockchain Unit Nonce} {ptr : Blockchain.Pointer Unit Nonce}
      (h : ptr ∈ b.spendable_ptrs) : ptr ∉ b.input_ptrs := by
    simp only [Blockchain.spendable_ptrs, Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset] at h
    exact h.2

  omit param in
  private lemma Blockchain.Pointer.not_spent_of_only_spender_not_mem
      {b : Blockchain Unit Nonce} {ptr : Blockchain.Pointer Unit Nonce} {tx : Transaction Unit Nonce}
      (honly : ∀ tx', tx' ∈ b → tx'.spends ptr → tx' = tx)
      (htx_not : tx ∉ b) :
      ptr ∉ b.input_ptrs := by
    intro hspent
    obtain ⟨tx', htx', hspends⟩ := Blockchain.Pointer.spent.of_tx b hspent
    exact htx_not ((honly tx' htx' hspends).symm ▸ htx')

  omit param in
  private lemma Blockchain.Transaction.input_ptrs_singleton_of_ninputs_eq_one
      (tx : Transaction Unit Nonce) (hn : tx.ninputs = 1) :
      tx.input_ptrs = [(tx.inputs.val[0]'(by rw [tx.inputs.property, hn]; omega)).outptr] := by
    rcases tx with ⟨ninputs, noutputs, inputs, witnesses, outputs, locktime⟩
    rcases inputs with ⟨inputs, hinputs⟩
    have hn' : ninputs = 1 := by simpa using hn
    unfold Blockchain.Transaction.input_ptrs
    simp only []
    rw [hn'] at hinputs
    cases inputs with
    | nil => simp at hinputs
    | cons hd tl =>
        cases tl with
        | nil => simp
        | cons hd₂ tl₂ => simp at hinputs

  omit param in
  private lemma Blockchain.Transaction.all_input_spendable_of_first
      (tx : Transaction Unit Nonce) (b : Blockchain Unit Nonce)
      (hn : tx.ninputs = 1) (hi : 0 < tx.inputs.val.length)
      (hfirst : (tx.inputs.val[0]'hi).outptr ∈ b.spendable_ptrs) :
      tx.all_input_spendable b := by
    unfold Blockchain.Transaction.all_input_spendable
    rw [Blockchain.Transaction.input_ptrs_singleton_of_ninputs_eq_one tx hn]
    simpa using hfirst

  omit param in
  private lemma Script.eval_relativeHeight_monotone
      (s : _root_.Script) (x : Blockchain.ScriptInput Unit Nonce) (rh' : ℕ)
      (hle : x.relativeHeight ≤ rh') :
      Blockchain.Script.eval s x →
        Blockchain.Script.eval s { x with relativeHeight := rh' } := by
    intro h
    rw [Script.eval_iff_Eval] at h ⊢
    cases h with
    | CommonFundS hcf =>
        cases hcf with
        | intro hp ha hb => exact Script.Eval.CommonFundS (CommonFund.Eval.intro hp ha hb)
    | ToRemote hrem =>
        cases hrem with
        | intro hp hsign hcsv =>
            rcases hcsv with ⟨hseq, hdelay_seq, hdelay_rel⟩
            exact Script.Eval.ToRemote
              (ToRemote.Eval.intro hp hsign ⟨hseq, hdelay_seq, le_trans hdelay_rel hle⟩)
    | ToLocal hloc =>
        cases hloc with
        | punish hp hsign hhash =>
            exact Script.Eval.ToLocal (ToLocal.Eval.punish hp hsign hhash)
        | regular hn hp hsign hcsv =>
            rcases hcsv with ⟨hseq, hdelay_seq, hdelay_rel⟩
            exact Script.Eval.ToLocal
              (ToLocal.Eval.regular hn hp hsign ⟨hseq, hdelay_seq, le_trans hdelay_rel hle⟩)

  omit param in
  private lemma signing_key_public_implies_corrupt (a : ℙ) (tr : 𝑇 Unit Nonce) :
      (key () Bytes.Kind.Key.Sign (nonce (Nonce.Sk a))).is_public Γ tr →
        TraceEvent.Corrupt a ∈ tr := by
    intro h
    have hc := is_public_key (Γ:=Γ) (tr:=tr) (p:=())
      (kind:=Bytes.Kind.Key.Sign) (n:={Nonce.Sk a}) (by simp) h
    simpa [Γ] using hc

  omit param in
  private lemma p2wsh_toLocal_communFound_scriptPubKey_ne
      (tl : _root_.ToLocal) (pks : ×× 𝒃) (amount₁ amount₂ : €) :
      (P2WSH.mkOutput (S:=Script) amount₁ (Script.ToLocal tl)).scriptPubKey ≠
        (P2WSH.mkOutput (S:=Script) amount₂
          (Script.CommonFundS (CommonFund.mk pks.a pks.b))).scriptPubKey := by
    intro h
    simp [P2WSH.from_S] at h
    change BytesEq.hash (α:=Unit) (η:=Nonce) ()
        (serialize (Script.ToLocal tl)) =
      BytesEq.hash (α:=Unit) (η:=Nonce) ()
        (serialize (Script.CommonFundS { pka := pks.a, pkb := pks.b })) at h
    have hnf : BytesEq.hash (α:=Unit) (η:=Nonce) ()
        (serialize (Script.ToLocal tl)) ≠ fail := by
      apply BytesEq.hash_fail' (p:=())
      · rfl
      · aapply Parsing.NotFailParsable.serialize_not_fail
    have hs := BytesEq.hash_inj ()
      (serialize (Script.ToLocal tl))
      (serialize (Script.CommonFundS { pka := pks.a, pkb := pks.b })) hnf h
    simp [Script.instParsable] at hs
    have hproj := congrArg (fun x : 𝕓 => BytesEq.proj_1 () x) hs
    simp at hproj
    have hconst := BytesEq.const_1_inj (α:=Unit) (η:=Nonce) hproj
    simp at hconst

  private lemma toLocal_output_of_base_outputs
      (b : Blockchain Unit Nonce) (ps : ×× ℙ) (self : AOrB)
      (common_fund : Blockchain.Pointer Unit Nonce) (balance : ×× ₿) (ohrk : 𝒃)
      (ptx : Blockchain.Transaction Unit Nonce)
      (houtputs_eq : ptx.outputs.val =
        (mk_base_transaction ps.vk self common_fund balance ohrk).outputs.val)
      (hptr : (ptx.mk_ptr self.toLocalVout).valid b) :
      b.get_output (ptx.mk_ptr self.toLocalVout) hptr =
        P2WSH.mkOutput (S:=Script)
          (b.get_output (ptx.mk_ptr self.toLocalVout) hptr).amount
          (Script.ToLocal {
            pk_regular := ps.vk[self],
            pk_punish := ps.vk[self.other],
            hrk_punish := ohrk,
            to_self_delay:=param.toSelfDelay
          }) := by
    apply Blockchain.Output.ext
    · rfl
    · cases self
      · have hvalid0 : Blockchain.VOUT.valid ptx (0:Blockchain.VOUT) := by
          have h1 := hptr.vout_valid
          simp [Blockchain.Transaction.mk_ptr] at h1
          have h2 := Blockchain.getElem_noutputs b ptx hptr.txid_valid
          rwa [h2] at h1
        have h0 := congrArg (fun xs : List (Blockchain.Output Unit Nonce) => xs[0]?) houtputs_eq
        simp [mk_base_transaction] at h0
        have htxout0 : ptx[(0:Blockchain.VOUT)]'hvalid0 = P2WSH.mkOutput balance.a
            (Script.ToLocal { pk_regular := ps.vk[AOrB.A], pk_punish := ps.vk[AOrB.B], hrk_punish := ohrk, to_self_delay:=param.toSelfDelay }) := by
          change ptx.outputs.val[0]'(by
            rw [ptx.outputs.property]
            exact hvalid0) = _
          have hsome : ptx.outputs.val[0]? = some (ptx.outputs.val[0]'(by
            rw [ptx.outputs.property]
            exact hvalid0)) := by rw [List.getElem?_eq_getElem]
          rw [hsome] at h0
          simpa using h0
        rw [Blockchain.Transaction.get_output_eq]
        simp [AOrB.toLocalVout] at htxout0 ⊢
        rw [htxout0]
      · have hvalid1 : Blockchain.VOUT.valid ptx (1:Blockchain.VOUT) := by
          have h1 := hptr.vout_valid
          simp [Blockchain.Transaction.mk_ptr] at h1
          have h2 := Blockchain.getElem_noutputs b ptx hptr.txid_valid
          rwa [h2] at h1
        have h1eq := congrArg (fun xs : List (Blockchain.Output Unit Nonce) => xs[1]?) houtputs_eq
        simp [mk_base_transaction] at h1eq
        have htxout1 : ptx[(1:Blockchain.VOUT)]'hvalid1 = P2WSH.mkOutput balance.b
            (Script.ToLocal { pk_regular := ps.vk[AOrB.B], pk_punish := ps.vk[AOrB.A], hrk_punish := ohrk, to_self_delay:=param.toSelfDelay }) := by
          change ptx.outputs.val[1]'(by
            rw [ptx.outputs.property]
            exact hvalid1) = _
          have hsome : ptx.outputs.val[1]? = some (ptx.outputs.val[1]'(by
            rw [ptx.outputs.property]
            exact hvalid1)) := by rw [List.getElem?_eq_getElem]
          rw [hsome] at h1eq
          simpa using h1eq
        rw [Blockchain.Transaction.get_output_eq]
        simp [AOrB.toLocalVout] at htxout1 ⊢
        rw [htxout1]

  omit param in
  private lemma p2wsh_toLocal_scriptPubKey_hrk_inj
      (tl₁ tl₂ : _root_.ToLocal) (amount₁ amount₂ : €)
      (h : (P2WSH.mkOutput (S:=Script) amount₁ (Script.ToLocal tl₁)).scriptPubKey =
           (P2WSH.mkOutput (S:=Script) amount₂ (Script.ToLocal tl₂)).scriptPubKey) :
      tl₁.hrk_punish = tl₂.hrk_punish := by
    let s₁ : Script := Script.ToLocal tl₁
    let s₂ : Script := Script.ToLocal tl₂
    have hser : (Parsing.Parsable.serialize (α:=𝕓) (β:=P2WSH Script) (P2WSH.from_S s₁)) =
        (Parsing.Parsable.serialize (α:=𝕓) (β:=P2WSH Script) (P2WSH.from_S s₂)) := by
      simpa [P2WSH.mkOutput, s₁, s₂] using congrArg BytesEq.NonFail.val h
    have hp2 : (P2WSH.from_S s₁ : P2WSH Script) = P2WSH.from_S s₂ := by
      exact Parsing.serialize_inj (γ:=𝕓) hser
    have hhash : BytesEq.hash () (Parsing.Parsable.serialize (α:=𝕓) (β:=Script) s₁) =
        BytesEq.hash () (Parsing.Parsable.serialize (α:=𝕓) (β:=Script) s₂) := by
      simpa [P2WSH.from_S] using congrArg P2WSH.hash hp2
    have hscript_ser : (Parsing.Parsable.serialize (α:=𝕓) (β:=Script) s₁) =
        (Parsing.Parsable.serialize (α:=𝕓) (β:=Script) s₂) := by
      apply BytesEq.hash_inj (p:=())
      · apply BytesEq.hash_fail'
        · rfl
        · apply Parsing.NotFailParsable.serialize_not_fail
      · exact hhash
    have hscript : s₁ = s₂ := by
      exact Parsing.serialize_inj (γ:=𝕓) hscript_ser
    subst s₁
    subst s₂
    cases tl₁
    cases tl₂
    simp only [Script.ToLocal.injEq, ToLocal.mk.injEq] at hscript
    tauto

  omit param in
  lemma Script.eval_toLocal_punish_of_relativeHeight_lt
      (tl : _root_.ToLocal) (x : Blockchain.ScriptInput Unit Nonce)
      (hrel : x.relativeHeight < tl.to_self_delay)
      (heval : Blockchain.Script.eval (Script.ToLocal tl) x) :
      ∃ sign rk,
        (do_parse x.witness.val as _root_.ToLocal.PunishRedeem) = some { sign, rk } ∧
        BytesEq.verify () sign.val tl.pk_punish.val = x.stripped.val ∧
        BytesEq.hash () rk.val = tl.hrk_punish.val := by
    rw [Script.eval_iff_Eval] at heval
    cases heval with
    | ToLocal hloc =>
        cases hloc with
        | punish hp hsign hhash => exact ⟨_, _, hp, hsign, hhash⟩
        | regular hn hp hsign hcsv =>
            rcases hcsv with ⟨_hseq, _hdelay_seq, hdelay_rel⟩
            omega

  private lemma toLocal_valid_input_defended
      {tr_final : 𝑇 Unit Nonce} {bfull : Blockchain Unit Nonce}
      {tx : Transaction Unit Nonce} {i : ℕ}
      (hv_trace : valid_trace Γ tr_final)
      (hbfull : bfull ≤ tr_final.get_blockchain)
      (hv_bfull : bfull.valid (P2WSH Script))
      (htx_mem : tx ∈ bfull)
      (hi : i < tx.inputs.length)
      (hptr : (tx.inputs.val[i]'(by simp [hi])).outptr.valid (tx.get_sub_blockchain bfull))
      (tl : _root_.ToLocal) (amount : €)
      (houtput : (tx.get_sub_blockchain bfull).get_output
          (tx.inputs.val[i]'(by simp [hi])).outptr hptr =
        P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl))
      (hrel : (tx.get_sub_blockchain bfull).height -
          ((tx.inputs.val[i]'(by simp [hi])).outptr.txid.get_block_idx (tx.get_sub_blockchain bfull) + 1) <
        tl.to_self_delay)
      (ps : ×× ℙ) (self : AOrB) (rk : 𝒃)
      (hpk : tl.pk_punish = ps.vk[self.other])
      (hhrk : tl.hrk_punish = rk_hash rk)
      (hnot_corrupt : TraceEvent.Corrupt ps[self.other] ∉ tr_final) :
      ∃ stx, (.Defended rk stx ∈' tr_final) ∧
        ∃ hptr', stx = tx.strip (tx.get_sub_blockchain bfull) i hi hptr' := by
    let bsub := tx.get_sub_blockchain bfull
    have htx_valid : tx.valid bsub (P2WSH Script) := by
      simpa [bsub] using hv_bfull tx htx_mem
    have hvpub_full : HasValidPublic.is_valid_public Γ tr_final.get_blockchain tr_final := by
      exact Blockchain.valid_public_of_valid_trace (Γ:=Γ) hv_trace
    have hvpub_bfull : HasValidPublic.is_valid_public Γ bfull tr_final := by
      exact Blockchain.is_valid_public_monotone' (Γ:=Γ) (tr:=tr_final) hbfull hvpub_full
    have htx_pub : Transaction.IsPublicValid tx Γ tr_final := by
      rw [Blockchain.instHasValidPublic.alt_def] at hvpub_bfull
      exact hvpub_bfull tx htx_mem
    have hinputmem : (i, (tx.inputs.val[i]'(by simp [hi]))) ∈ tx.inputs.val.enumerate_from 0 := by
      have hm : (tx.inputs.val.enumerate_from 0)[i]'(by simpa [List.enumerat_from_length] using hi) ∈
          tx.inputs.val.enumerate_from 0 := List.getElem_mem _
      simpa [List.enumerate_from_get_elem tx.inputs.val 0 i (by simpa using hi)] using hm
    have hscripts := htx_valid.valid_scripts
    unfold Blockchain.Transaction.valid_eval_scripts at hscripts
    rw [List.forall_iff_forall_mem] at hscripts
    specialize hscripts _ hinputmem
    cases hscripts with
    | intro input hi' hin hptrin s hparse heval =>
      have hinput_eq : input = tx.inputs.val[i]'(by simp [hi]) := by
        simpa using hin.symm
      subst input
      have houtput' : bsub.get_output (tx.inputs.val[i]'(by simp [hi])).outptr hptrin =
          P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl) := by
        simpa [bsub] using houtput
      have hs : s = P2WSH.from_S (Script.ToLocal tl) := by
        have hp := hparse
        change parse (bsub.get_output (tx.inputs.val[i]'(by simp [hi])).outptr hptrin).scriptPubKey.val = some s at hp
        rw [houtput'] at hp
        simp [P2WSH.from_S] at hp
        exact hp.symm
      subst s
      rw [P2WSH.eval_iff_Eval] at heval
      cases heval with
      | @intro args script inner_s p2h x hargs hh hs hrec =>
        have hscript_bytes : script.val = serialize (Script.ToLocal tl) := by
          apply BytesEq.hash_inj (p:=()) (a:=script.val)
          · apply BytesEq.hash_fail'
            · rfl
            · exact script.prop
          · simpa [P2WSH.from_S] using hh
        rw [hscript_bytes, Parsing.Parsable.sound] at hs
        cases hs
        have hrel_x :
            ({ arg := (tx.inputs.val[i]'(by simp [hi'])).scriptSig
               witness := args
               stripped := ⟨Parsing.Parsable.serialize (tx.strip bsub i hi' hptrin),
                 by aapply Parsing.NotFailParsable.serialize_not_fail⟩
               sequence := (tx.inputs.val[i]'(by simp [hi'])).sequence
               locktime := tx.locktime
               relativeHeight := bsub.height -
                 ((tx.inputs.val[i]'(by simp [hi'])).outptr.txid.get_block_idx bsub + 1) } :
                Blockchain.ScriptInput Unit Nonce).relativeHeight < tl.to_self_delay := by
          simpa [bsub] using hrel
        have hpun := Script.eval_toLocal_punish_of_relativeHeight_lt tl _ hrel_x hrec
        rcases hpun with ⟨sign_pun, rk_pun, hp_wit, hverify, hhash⟩
        have hwit_vp : HasValidPublic.is_valid_public Γ
            (tx.witnesses.val[i]'(by simp [hi'])) tr_final := by
          exact htx_pub.witnesses _ (List.getElem_mem _)
        have hp2wsh_wit_vp : HasValidPublic.is_valid_public Γ
            ({ args := args, script := script } : P2WSH.Witness) tr_final := by
          apply Parsing.ValidParsable.valid_parse (Γ:=Γ) (tr:=tr_final)
            (x:=(tx.witnesses.val[i]'(by simp [hi'])).val)
          · exact hwit_vp
          · simpa using hargs
        have hargs_vp : HasValidPublic.is_valid_public Γ args tr_final := by
          rcases hp2wsh_wit_vp with ⟨hargs_vp, _⟩
          exact hargs_vp
        have hredeem_vp : HasValidPublic.is_valid_public Γ
            ({ sign := sign_pun, rk := rk_pun } : ToLocal.PunishRedeem) tr_final := by
          apply Parsing.ValidParsable.valid_parse (Γ:=Γ) (tr:=tr_final) (x:=args.val)
          · exact hargs_vp
          · simpa using hp_wit
        have hsign_vp : HasValidPublic.is_valid_public Γ sign_pun tr_final := by
          rcases hredeem_vp with ⟨hsign_vp, _⟩
          exact hsign_vp
        have hptr_actual : (tx.inputs.val[i]'(by simp [hi])).outptr.valid bsub := by
          simpa using hptrin
        let actual_strip := tx.strip bsub i hi hptr_actual
        -- The stripped transaction's scriptcode is the ToLocal output's scriptPubKey.
        have hactual_tl_script : actual_strip.scriptcode =
            (P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl)).scriptPubKey := by
          dsimp [actual_strip]
          simp [Blockchain.Transaction.strip, bsub]
          exact congrArg Blockchain.Output.scriptPubKey houtput'
        have hverify_nf : verify () sign_pun.val tl.pk_punish.val ≠ fail := by
          rw [hverify]
          apply Parsing.NotFailParsable.serialize_not_fail
        obtain ⟨m_sig, k_sig, hpred, hsign_eq, hk_valid, hvk_eq⟩ :=
          Crypto.valid_verify (Γ:=Γ) (p:=()) (σ:=sign_pun.val) (k:=tl.pk_punish.val)
            (tr:=tr_final) hverify_nf (BytesEq.is_valid_public_valid sign_pun hsign_vp)
        have hk_sig : k_sig = nonce (Nonce.Sk ps[self.other]) := by
          symm
          apply BytesEq.key_inj (p:=()) (kind:=Bytes.Kind.Key.Verify)
          rw [← hvk_eq, hpk]
          cases self <;> simp [AAndB.vk, BytesEq.vk]
        have hm_sig : m_sig = serialize actual_strip := by
          have hvs := BytesEq.verify_sign () m_sig k_sig rfl (by rw [hk_sig]; prove_not_fail)
          rw [hsign_eq, hvk_eq] at hverify
          rw [hvs] at hverify
          exact hverify
        have hnot_base {m k : 𝕓} (hm : m = serialize actual_strip)
            (hbase : sign_tx_pred_base tr_final m k) : False := by
          cases hbase with
          | intro b_base ps_base tx_owner signer signer_rk commitment_hrk hkey cf_ptr cf_ptr_valid cf_ptr_is_cf balance cf_funds_eq hevs def_m =>
            have hstrip_base : actual_strip =
                (mk_base_transaction ps_base.vk tx_owner cf_ptr balance commitment_hrk).strip b_base 0
                  (by simp [mk_base_transaction]) cf_ptr_valid := by
              apply (Parsing.serialize_inj (γ:=𝕓))
              rw [← hm]
              simpa using def_m
            have hbase_cf :
                actual_strip.scriptcode =
                  (P2WSH.mkOutput (S:=Script)
                    ((b_base.get_output cf_ptr cf_ptr_valid).amount)
                    (Script.CommonFundS (CommonFund.mk ps_base.vk.a ps_base.vk.b))).scriptPubKey := by
              rw [hstrip_base]
              simp [Blockchain.Transaction.strip, mk_base_transaction]
              exact congrArg Blockchain.Output.scriptPubKey cf_ptr_is_cf
            have hbad :
                (P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl)).scriptPubKey =
                  (P2WSH.mkOutput (S:=Script)
                    ((b_base.get_output cf_ptr cf_ptr_valid).amount)
                    (Script.CommonFundS (CommonFund.mk ps_base.vk.a ps_base.vk.b))).scriptPubKey := by
              rw [← hactual_tl_script, hbase_cf]
            exact p2wsh_toLocal_communFound_scriptPubKey_ne tl ps_base.vk _ _ hbad
        have hrk_eq : rk_pun = rk := by
          apply BytesEq.NonFail.ext
          have hhash' : BytesEq.hash () rk_pun.val = BytesEq.hash () rk.val := by
            rw [hhash]
            exact (congrArg BytesEq.NonFail.val hhrk).trans (by rfl)
          exact BytesEq.hash_inj () rk_pun.val rk.val (by cases rk_pun; prove_not_fail) hhash'
        cases hpred with
        | inl hpub =>
            exfalso
            exact hnot_corrupt (signing_key_public_implies_corrupt ps[self.other] tr_final (by simpa [hk_sig] using hpub))
        | inr hu =>
            cases hu with
            | inl hbase => exact False.elim (hnot_base hm_sig (by rwa [hk_sig] at hbase))
            | inr hpunish =>
                cases hpunish with
                | intro ps_pun self_pun rk_sig stx hdefended hkey_pun hrk_pun hhash_pun hscript_pun def_m =>
                    have hstx : stx = actual_strip := by
                      apply (Parsing.serialize_inj (γ:=𝕓))
                      rw [← hm_sig]
                      simpa using def_m.symm
                    have hpun_script :
                        actual_strip.scriptcode =
                          (P2WSH.mkOutput (S:=Script) stx.amount
                            (Script.ToLocal {
                              pk_regular := ps_pun.vk[self_pun],
                              pk_punish := ps_pun.vk[self_pun.other],
                              hrk_punish := hrk_pun,
                              to_self_delay := param.toSelfDelay })).scriptPubKey := by
                      rw [← hstx]
                      exact hscript_pun
                    have hhrk_pun : hrk_pun = tl.hrk_punish := by
                      let tl_pun : _root_.ToLocal := {
                        pk_regular := ps_pun.vk[self_pun],
                        pk_punish := ps_pun.vk[self_pun.other],
                        hrk_punish := hrk_pun,
                        to_self_delay := param.toSelfDelay }
                      have hspk_eq :
                          (P2WSH.mkOutput (S:=Script) stx.amount (Script.ToLocal tl_pun)).scriptPubKey =
                            (P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl)).scriptPubKey := by
                        simpa [tl_pun] using hpun_script.symm.trans hactual_tl_script
                      exact p2wsh_toLocal_scriptPubKey_hrk_inj tl_pun tl stx.amount amount hspk_eq
                    have hrk_sig_eq : rk_sig = rk := by
                      apply BytesEq.NonFail.ext
                      have hhash_sig : BytesEq.hash () rk_sig.val = BytesEq.hash () rk.val := by
                        rw [hhash_pun, hhrk_pun, hhrk]
                      exact BytesEq.hash_inj () rk_sig.val rk.val
                        (by cases rk_sig; prove_not_fail) hhash_sig
                    refine ⟨actual_strip, ?_, ?_⟩
                    · simpa [hstx, hrk_sig_eq] using hdefended
                    · refine ⟨hptr_actual, ?_⟩
                      rfl

  omit param in
  private lemma P2WSH.Script.eval_relativeHeight_monotone
      (s : P2WSH _root_.Script) (x : Blockchain.ScriptInput Unit Nonce) (rh' : ℕ)
      (hle : x.relativeHeight ≤ rh') :
      Blockchain.Script.eval s x →
        Blockchain.Script.eval s { x with relativeHeight := rh' } := by
    intro h
    rw [P2WSH.eval_iff_Eval] at h ⊢
    cases h with
    | intro hargs hh hs hrec =>
        rename_i args script inner_s h
        constructor
        · exact hargs
        · exact hh
        · exact hs
        · exact _root_.Script.eval_relativeHeight_monotone inner_s {x with witness := args}
            rh' (by simpa using hle) hrec

  omit param in
  private lemma Blockchain.Transaction.strip.grows_transactions_prefix
      {b b' : Blockchain Unit Nonce} {tx : Transaction Unit Nonce}
      (hprefix : b.transactions <+: b'.transactions)
      (i : ℕ)
      (hi : i < tx.inputs.length)
      (hptr : (tx.inputs.val[i]'(by simp [hi])).outptr.valid b) :
      tx.strip b i hi hptr =
        tx.strip b' i hi (Blockchain.Pointer.valid_of_transactions_prefix hprefix hptr) := by
    let input := tx.inputs.val[i]'(by simp [hi])
    have hout : b.get_output input.outptr hptr =
        b'.get_output input.outptr (Blockchain.Pointer.valid_of_transactions_prefix hprefix hptr) := by
      exact Blockchain.get_output_stable_prefix (b := b) (b' := b')
        (ptr := input.outptr) hprefix hptr
    simp [Blockchain.Transaction.strip]
    exact ⟨congrArg Blockchain.Output.scriptPubKey hout,
      congrArg Blockchain.Output.amount hout⟩

  omit param in
  private lemma Blockchain.Transaction.valid_of_prefix_of_spendable
      {b b' : Blockchain Unit Nonce} {tx : Transaction Unit Nonce}
      (hb : b ≤ b') (hnonzero : tx.ninputs ≠ 0)
      (hv : tx.valid b (P2WSH _root_.Script))
      (hsp : tx.all_input_spendable b') :
      tx.valid b' (P2WSH _root_.Script) := by
    constructor
    case unique =>
      intro hzero
      exact False.elim (hnonzero hzero)
    case spendable =>
      exact hsp
    case balance =>
      intro hne
      have hbal := hv.balance hne
      unfold Transaction.valid_balance at hbal ⊢
      have hvptr_b : tx.valid_ptrs b :=
        Transaction.all_input_spendable_is_valid_ptrs (b := b) (tx := tx) hv.spendable
      have hvptr_b' : tx.valid_ptrs b' :=
        Transaction.all_input_spendable_is_valid_ptrs (b := b') (tx := tx) hsp
      have hinput_value :
          tx.input_value b' (by exact hvptr_b') = tx.input_value b (by exact hvptr_b) := by
        unfold Transaction.input_value Pointer.value
        simp only [List.map_eq_map]
        congr 1
        apply List.map_congr_left
        intro input _hin
        have hptr_b : input.val.outptr.valid b := by
          exact Transaction.valid_ptrs_valid (b := b) (tx := tx) (input := input.val)
            hvptr_b input.property
        have hout := Blockchain.get_output_stable
          (b := b) (b' := b') (ptr := input.val.outptr) hb hptr_b
        exact (congrArg Blockchain.Output.amount hout).symm
      rwa [hinput_value]
    case valid_scripts =>
      have hvscripts := hv.valid_scripts
      unfold Transaction.valid_eval_scripts at hvscripts ⊢
      rw [List.forall_iff_forall_mem] at hvscripts ⊢
      intro pair hpair
      specialize hvscripts pair hpair
      rcases pair with ⟨i, _input_pair⟩
      cases hvscripts with
      | intro input hi hin hptrin s hparse eval_true =>
          have hptrin' : input.outptr.valid b' :=
            Blockchain.Pointer.valid_monotone (ptr := input.outptr) hb hptrin
          have hout := Blockchain.get_output_stable
            (b := b) (b' := b') (ptr := input.outptr) hb hptrin
          have hparse' :
              Parsing.Parsable.parse (α := 𝐵 Unit Nonce) (β := P2WSH _root_.Script)
                (b'.get_output input.outptr hptrin').scriptPubKey.val = some s := by
            rw [← congrArg (fun out : Blockchain.Output Unit Nonce => out.scriptPubKey.val) hout]
            exact hparse
          have hptr_i_b : (tx.inputs.val[i]'(by simp [hi])).outptr.valid b := by
            rw [hin]
            exact hptrin
          have hptr_i_b' : (tx.inputs.val[i]'(by simp [hi])).outptr.valid b' :=
            Blockchain.Pointer.valid_monotone
              (ptr := (tx.inputs.val[i]'(by simp [hi])).outptr) hb hptr_i_b
          have hstrip : tx.strip b i hi hptr_i_b = tx.strip b' i hi hptr_i_b' := by
            exact Transaction.strip.grows (b := b) (tx := tx) (i := i) (hi := hi)
              (hptr := hptr_i_b) b' hb
          have hrelativeHeight_le :
              b.height - (input.outptr.txid.get_block_idx b + 1) ≤
                b'.height - (input.outptr.txid.get_block_idx b' + 1) := by
            have hidx : input.outptr.txid.get_block_idx b = input.outptr.txid.get_block_idx b' :=
              Blockchain.TXID.get_block_idx_stable (b := b) (b' := b')
                (txid := input.outptr.txid) hptrin.txid_valid hb
            have hheight_le : b.height ≤ b'.height := Blockchain.height_monotone hb
            omega
          refine Blockchain.Input.valid_eval_scripts.intro
            (b := b') (tx := tx) (script_t := P2WSH _root_.Script)
            input hi hin hptrin' s hparse' ?_
          have heval_stripped :
              Blockchain.Script.eval s
                { arg := input.scriptSig
                  witness := tx.witnesses.val[i]'(by simp [hi])
                  stripped := ⟨Parsing.Parsable.serialize (tx.strip b' i hi hptr_i_b'),
                    by aapply Parsing.NotFailParsable.serialize_not_fail⟩
                  sequence := input.sequence
                  locktime := tx.locktime
                  relativeHeight := b.height - (input.outptr.txid.get_block_idx b + 1) } := by
            simpa [hptr_i_b, hptr_i_b', hstrip] using eval_true
          exact P2WSH.Script.eval_relativeHeight_monotone s _
            (b'.height - (input.outptr.txid.get_block_idx b' + 1))
            hrelativeHeight_le heval_stripped

  omit param in
  lemma Blockchain.Pointer.relativeHeight_lt_of_tip_and_height_le
      {b b' : Blockchain Unit Nonce} {ptr : Blockchain.Pointer Unit Nonce}
      {budget delay : ℕ}
      (hptr : ptr.valid b) (hb : b ≤ b')
      (htip : ptr.txid.get_block_idx b + 1 = b.height)
      (hheight : b'.height ≤ b.height + budget)
      (hbudget : budget < delay) :
      b'.height - (ptr.txid.get_block_idx b' + 1) < delay := by
    have hidx : ptr.txid.get_block_idx b = ptr.txid.get_block_idx b' :=
      Blockchain.TXID.get_block_idx_stable (b := b) (b' := b')
        (txid := ptr.txid) hptr.txid_valid hb
    omega

  lemma Blockchain.Pointer.relativeHeight_lt_toSelfDelay_of_punish_window
      {ptr : Blockchain.Pointer Unit Nonce} {tr_mid : 𝑇 Unit Nonce}
      (hptr : ptr.valid tr.get_blockchain)
      (hgrow_mid : tr ≤ tr_mid)
      (htip : ptr.txid.get_block_idx tr.get_blockchain + 1 = tr.get_blockchain.height)
      (hheight_mid : tr_mid.get_blockchain.height ≤
        tr.get_blockchain.height + (punish_time + miner_time))
      (htime_budget : punish_time + miner_time < param.toSelfDelay) :
      tr_mid.get_blockchain.height -
          (ptr.txid.get_block_idx tr_mid.get_blockchain + 1) < param.toSelfDelay := by
    exact Blockchain.Pointer.relativeHeight_lt_of_tip_and_height_le
      (b := tr.get_blockchain) (b' := tr_mid.get_blockchain) (ptr := ptr)
      (budget := punish_time + miner_time) (delay := param.toSelfDelay)
      hptr (List.get_blockchain_monotone hgrow_mid) htip hheight_mid htime_budget

  omit param in
  private lemma List.exists_head?_eq_some_of_exists_mem {α} {xs : List α}
      (h : ∃ x, x ∈ xs) : ∃ x, xs.head? = some x := by
    rcases h with ⟨x, hx⟩
    cases xs with
    | nil => cases hx
    | cons hd tl => exact ⟨hd, rfl⟩

  private lemma old_valid_of_mem
      (hv : valid_trace Γ tr) (hold : Evs.Old {ps, self, common_fund, i, rk, balance} ∈' tr) :
      event_preds.OldValid tr ps self common_fund i balance rk := by
    have hvt := Crypto.valid_trace_mem (Γ := Γ)
      (ev := (TraceEvent.Event ⟨"", serialize (Evs.Old {ps, self, common_fund, i, rk, balance})⟩ : 𝑇𝐸 Unit Nonce))
      (tr := tr) hv (by simpa using hold)
    simpa [Crypto.valid_trace_event, UserPreds.u_valid_event] using hvt

  lemma punish_emits_postdefended
      (i : ℕ) (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
      (b : Blockchain Unit Nonce) (s : StdState) (pc : PcState) (rk : 𝒃)
      (hpc_old : s.pc_old = some pc)
      (hready : pc.IsComplete)
      (hrk : pc.other_rk = some rk)
      (hhead : ∃ ptx,
        (punishable_transactions s.self s.ps b s.common_fund pc).head? = some ptx ∧
        (ptx.mk_ptr s.self.toLocalVout).valid b) :
      ∃ tx, .PostDefended s.common_fund rk tx ∈'
        (punish noutputs outputs i
          (serialize (β := WithBlockchain Unit) {blockchain := b, msg := ()})
          (.Std s)).as_list_including := by
    rcases hhead with ⟨ptx, hhead, hptr⟩
    rcases s with ⟨self, ps, common_fund, amount, pc_new, pc_old⟩
    simp only at hpc_old hrk hhead ⊢
    cases hpc_old
    cases hready with
    | intro =>
    simp only at hrk
    cases hrk
    unfold punish
    rw[List.head?_eq_some_iff] at hhead
    obtain ⟨_, hhead⟩ := hhead
    simp at hptr
    simp [Parsing.Parsable.sound, Atom.fromOption, bind, Option.bind, hhead, hptr, dguard, exists_or]

  private lemma punish_emits_postdefended_strong
      (i : ℕ) (noutputs: € → ℕ) (outputs: (n:€) → Blockchain.Output Unit Nonce *** (noutputs n))
      (b : Blockchain Unit Nonce) (s : StdState) (pc : PcState) (rk : 𝒃)
      (hpc_old : s.pc_old = some pc)
      (hready : pc.IsComplete)
      (hrk : pc.other_rk = some rk)
      (hhead : ∃ ptx,
        (punishable_transactions s.self s.ps b s.common_fund pc).head? = some ptx ∧
        (ptx.mk_ptr s.self.toLocalVout).valid b) :
      ∃ tx ptx,
        (punishable_transactions s.self s.ps b s.common_fund pc).head? = some ptx ∧
        (.PostDefended s.common_fund rk tx ∈'
          (punish noutputs outputs i
            (serialize (β := WithBlockchain Unit) {blockchain := b, msg := ()})
            (.Std s)).as_list_including) ∧
        (∃ h₀ hptr,
          (.Defended rk (tx.strip b 0 h₀ hptr) ∈'
            (punish noutputs outputs i
              (serialize (β := WithBlockchain Unit) {blockchain := b, msg := ()})
              (.Std s)).as_list_including)) ∧
        tx.ninputs = 1 ∧
        (∃ hfirst : 0 < tx.inputs.val.length,
          (tx.inputs.val[0]'hfirst).outptr = ptx.mk_ptr s.self.toLocalVout) := by
    rcases hhead with ⟨ptx, hhead, hptr⟩
    rcases s with ⟨self, ps, common_fund, amount, pc_new, pc_old⟩
    simp only at hpc_old hrk hhead ⊢
    cases hpc_old
    cases hready with
    | intro =>
    rename_i pc_self pc_balance pc_self_rk pc_other_rk pc_other_hrk pc_signed pc_i
    simp only at hrk
    cases hrk
    rw[List.head?_eq_some_iff] at hhead
    obtain ⟨_, hhead_mem⟩ := hhead
    simp at hptr
    let amt := ((ptx[self.toLocalVout]?).getD 0).amount
    let script_S := (Script.ToLocal {
      pk_regular:=ps.vk[self],
      pk_punish:=ps.vk[self.other], hrk_punish:=pc_other_hrk,
      to_self_delay:=param.toSelfDelay})
    let unsigned_tx : Transaction Unit Nonce := {
      outputs:= outputs amt
      ninputs := 1
      noutputs := noutputs amt
      inputs := ⟨[
        P2WSH.mkInput (ptx.mk_ptr self.toLocalVout) 0 script_S 0
      ], rfl⟩
      witnesses := ⟨[0], rfl⟩
      locktime := 0
    }
    have hptr_unsigned : (unsigned_tx.inputs.val[0]'(by simp [unsigned_tx])).outptr.valid b := by
      simpa [unsigned_tx, P2WSH.mkInput] using hptr
    let tx_stripped := unsigned_tx.strip b 0 (by simp [unsigned_tx]) hptr_unsigned
    let signature := sign () (serialize tx_stripped) (sk ps[self.other])
    let witness: ToLocal.PunishRedeem := by
      refine { sign := ⟨signature, ?nf₂⟩, rk := rk }
      aapply BytesEq.sign_fail'; rfl
      aapply Parsing.NotFailParsable.serialize_not_fail
      aapply BytesEq.nonce_fail
    let witness_S : P2WSH.Witness := {
      args := ⟨serialize witness, by aapply Parsing.NotFailParsable.serialize_not_fail⟩,
      script := ⟨serialize script_S, by aapply Parsing.NotFailParsable.serialize_not_fail⟩
    }
    let final_tx : Transaction Unit Nonce :=
      {unsigned_tx with witnesses:=⟨[⟨(serialize witness_S), by aapply Parsing.NotFailParsable.serialize_not_fail⟩], rfl⟩ }
    refine ⟨final_tx, ptx, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhead_mem]
      rfl
    · simp [punish, Parsing.Parsable.sound, Atom.fromOption, bind, Option.bind,
        hhead_mem, hptr, dguard, amt, script_S, unsigned_tx, tx_stripped,
        signature, witness, witness_S, final_tx]
    · refine ⟨by simp [final_tx, unsigned_tx], ?_, ?_⟩
      · simpa [final_tx, unsigned_tx, P2WSH.mkInput] using hptr
      · simp [punish, Parsing.Parsable.sound, Atom.fromOption, bind, Option.bind,
          hhead_mem, hptr, dguard, amt, script_S, unsigned_tx, tx_stripped,
          signature, witness, witness_S, final_tx]
        right
        rfl
    · simp [final_tx, unsigned_tx]
    · refine ⟨by simp [final_tx, unsigned_tx], ?_⟩
      simp [final_tx, unsigned_tx, P2WSH.mkInput]


  def Evs.get_state (e: Evs): StdState := Option.iget $ do
    let .Old {ps, self, common_fund, i, rk, balance} := e | return default
    let ⟨_,_⟩ <- dguard (i < tr.length)
    let .SetState s := tr.get_at i | return default
    let .Std s <- do_parse s as State | return default
    return s

  lemma punish.get_state.correct
    (hv₁: valid_trace Γ tr):
      let evs := .Old {ps, self, common_fund, i, rk, balance}
      let s := evs.get_state tr
      (hin: evs ∈' tr) →
      ∃ pc,
      Trace.IsStateAt tr i (State.Std s) ∧
      s.pc_old = some pc ∧ pc.IsComplete ∧ pc.other_rk = some rk := by
      intro evs s hin
      aapply Crypto.valid_trace_mem at hin
      simp only [valid_trace_event, valid_event, u_valid_event, Parsing.Parsable.sound, evs] at hin
      rcases hin with ⟨ht, hin', hparse, hps, hcommon_fund, hpc_old, hready, hrk⟩
      rename_i s₀ s' pc _ _
      exists pc
      generalize heq: s = s'' at *
      simp[Evs.get_state, s, evs, dguard, Option.iget, *] at heq
      cases heq
      tauto

  omit param in
  lemma punish.get_state.correct' (h)
      (hin: tr.get_at i h = .SetState s₀) (hparse : (do_parse s₀ as State) = some (.Std s))
    : s = (Evs.Old {ps, self, common_fund, i, rk, balance}).get_state tr := by simp [Evs.get_state, dguard, *]

  /-- Given `.Old {ps, self, common_fund, i, rk, balance} ∈' tr`, the state `s`
  extracted by `Evs.get_state` reproduces every field of the `Old` event: its
  `ps`, `self`, `common_fund` match, its `pc_old` is some complete `PcState`
  `pc_oldv`, and `pc_oldv.balance` matches.

  This bundles the `old_valid_of_mem` + `punish.get_state.correct'` dance that
  was previously inlined (once in `punish.sound`, four times in
  `punish.sound'_strong`). -/
  lemma punish.get_state.fields
      (hv₁: valid_trace Γ tr)
      (hold: .Old {ps, self, common_fund, i, rk, balance} ∈' tr) :
      let evs : Evs := .Old {ps, self, common_fund, i, rk, balance}
      let s := evs.get_state tr
      ∃ pc_oldv,
        s.ps = ps ∧ s.self = self ∧ s.common_fund = common_fund ∧
        s.pc_old = some pc_oldv ∧ pc_oldv.balance = balance := by
    intro evs s
    have h_old_valid := old_valid_of_mem (tr := tr) (ps := ps) (self := self)
      (common_fund := common_fund) (i := i) (rk := rk) (balance := balance) hv₁ hold
    cases h_old_valid with
    | @intr s₀ s_old pc_oldv ht hin' hparse hps hself hcommon_fund hpc_oldv hreadyv hrkv hbalancev =>
      have hs_eq : s = s_old := by
        symm
        exact punish.get_state.correct' tr ht hin' hparse
          (rk:=rk) (common_fund:=common_fund) (ps:=ps) (self:=self) (balance:=balance)
      refine ⟨pc_oldv, hs_eq.symm ▸ hps, hs_eq.symm ▸ hself, hs_eq.symm ▸ hcommon_fund,
              hs_eq.symm ▸ hpc_oldv, hbalancev⟩


  -- for the simp later
  set_option synthInstance.maxHeartbeats 300000 in
  local instance {s: StdState} {tx: Transaction Unit Nonce} : Decidable
    (x ∈
      guard (f:=List)
        (tx.outputs.val =
          (mk_base_transaction
                { a := { val := key () Bytes.Kind.Key.Verify (xor_set {Nonce.Sk s.ps.a}), prop := (by prove_not_fail) },
                  b := { val := key () Bytes.Kind.Key.Verify (xor_set {Nonce.Sk s.ps.b}), prop := (by prove_not_fail) } }
                s.self s.common_fund
                (s.pc_old.getD default).balance
                x'').outputs.val)) := inferInstance

  omit param in
  lemma List.guard_def [Decidable P] (x:Unit): x ∈ (guard (f:=List) P) ↔ P := by
    by_cases h: P <;> simp[guard, failure, h]

  omit param in
  lemma List.dguard_def [Decidable P] (a) (b:P): (⟨a, b⟩ ∈ dguard (f:=List) P) ↔ P := by
      by_cases h: P <;> simp[dguard, failure, h]


  lemma punishable_transactions_toLocalVout_valid
      (b : Blockchain Unit Nonce) (hv : b.valid (P2WSH Script))
      (ps : ×× ℙ) (self : AOrB) (common_fund : Pointer Unit Nonce)
      (pc : PcState) (ptx : Transaction Unit Nonce)
      (hcomplete : pc.IsComplete)
      (hmem : ptx ∈ punishable_transactions self ps b common_fund pc) :
      (ptx.mk_ptr self.toLocalVout).valid b := by
    have htxmem_list : ptx ∈ b.transactions := by
      exact punishable_transactions.mem_transactions (self := self) (ps := ps) (b := b)
        (common_fund := common_fund) (state := pc) hmem
    have htxmem : ptx ∈ b := by
      rw [Blockchain.mem_alt_def]
      exact htxmem_list
    cases hcomplete
    rename_i pcself pcbal pcself_rk rk other_hrk signed pci
    have hout := punishable_transactions.mem_outputs_complete (self := self) (ps := ps) (b := b)
      (common_fund := common_fund) (balance := pcbal) (self_rk := pcself_rk) (rk := rk)
      (other_hrk := other_hrk) (signed := signed) (i := pci) (tx := ptx) hmem
    refine ⟨?_, ?_⟩
    · simpa [Blockchain.Transaction.mk_ptr] using Blockchain.tx_mem_txid_valid (b := b) (tx := ptx) htxmem
    · have hnodup := Blockchain.valid_impl_no_duplicates (b := b) (script_t := P2WSH Script) hv
      have hget := hnodup ptx htxmem
      simp [Blockchain.Transaction.mk_ptr]
      rw [hget]
      have hlen : ptx.outputs.val.length = 2 := by
        simpa [mk_base_transaction] using congrArg List.length hout
      rw [← ptx.outputs.property]
      cases self
      · change (0:ℕ) < ptx.outputs.val.length
        omega
      · change (1:ℕ) < ptx.outputs.val.length
        omega

  lemma punish_CommonFund_spent_by_hrk_strong_enough
    (ps:×× ℙ) (common_fund)
    (hv₁: valid_trace Γ tr) (hv₂: tr.get_blockchain.valid (P2WSH Script))
    (hcfv)
    (h_cm: CommonFund.spent_by_hrk (tr.get_blockchain) ps common_fund hv₂ hcfv self (rk_hash rk) balance)
    (h_old': .Old {ps, self, common_fund, i, rk, balance} ∈' tr):
      let s := (Evs.Old {ps, self, common_fund, i, rk, balance}).get_state tr
      ∃ pc ptx,
        (s.pc_old = some pc) ∧
        pc.IsComplete ∧
        pc.other_rk = some rk ∧
        (punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc).head? = some ptx ∧
        (ptx.mk_ptr s.self.toLocalVout).valid (tr.get_blockchain) ∧
        ptx.outputs.val =
          (mk_base_transaction s.ps.vk s.self s.common_fund pc.balance (rk_hash rk)).outputs.val := by
    intro s
    obtain ⟨pc, h_is_state, heq_pc, h_pc_complete, h_pc_other_rk⟩ := punish.get_state.correct tr hv₁ h_old'
    have hgetD : s.pc_old.getD default = pc := by
      unfold s
      rw [heq_pc]
      rfl

    -- `s` reproduces the fields of the `.Old` event; in particular `s.pc_old = some pc_oldv`
    -- and `pc_oldv.balance = balance`, and `pc = pc_oldv` follows from `heq_pc`.
    obtain ⟨pc_oldv, hps_s, hself_s, hcommon_fund_s, hpc_oldv, hbalance⟩ :=
      punish.get_state.fields tr hv₁ h_old'
    have hps_s : s.ps = ps := hps_s
    have hself_s : s.self = self := hself_s
    have hcommon_fund_s : s.common_fund = common_fund := hcommon_fund_s
    have hv₃ : HasValid.valid Γ s tr := by aapply Trace.IsStateAt.valid at h_is_state
    have hpc_eq : pc = pc_oldv := by grind
    cases hpc_eq

    obtain ⟨tx, hin_tx, h_spent, j, hj, hstrip⟩ := h_cm
    let base_hrk : 𝒃 := rk_hash rk
    have hinputs : tx.input_ptrs = [common_fund] := by
      have := congrArg Blockchain.StripedTransaction.inputs hstrip
      simpa [base_hrk, rk_hash, Blockchain.Transaction.strip, mk_base_transaction, Transaction.input_ptrs] using this
    have h0 : 0 < tx.ninputs := by
      have hlen := congrArg List.length hinputs
      simp [Transaction.input_ptrs] at hlen
      omega
    have hj_eq : j = 0 := by
      have hlen := congrArg List.length hinputs
      simp [Transaction.input_ptrs] at hlen
      omega
    have hptr0 : Pointer.valid tr.get_blockchain (tx.inputs.val[0]'(by simp [h0])).outptr := by
      exact Blockchain.Transaction.strip_valid_ptr (script_t := P2WSH Script)
        tr.get_blockchain tx 0 hv₂ hin_tx h0
    have hstrip0 :
        tx.strip tr.get_blockchain 0 h0 hptr0 =
          (mk_base_transaction ps.vk self common_fund balance base_hrk).strip tr.get_blockchain 0
            (by simp [mk_base_transaction]) hcfv := by
      subst j
      simpa [base_hrk, rk_hash] using hstrip
    have hout_base :
        tx.outputs.val = (mk_base_transaction ps.vk self common_fund balance base_hrk).outputs.val := by
      have := congrArg Blockchain.StripedTransaction.outputs hstrip0
      simpa [Blockchain.Transaction.strip] using this

    have hpc_inv_ex : ∃ (hcfv_s : Pointer.valid tr.get_blockchain s.common_fund),
        PcState.Invariant Γ s.self s.common_fund s.amount tr s.ps hcfv_s pc := by
      rcases hv₃ with ⟨hcfv_s, hvfpv₃, ha₃, hcf₃, hpc_new₃, hpc_old₃⟩
      have hpc_old_s : s.pc_old.NoneOrP
          (fun x => PcState.Invariant Γ s.self s.common_fund s.amount tr s.ps hcfv_s x) := by
        simpa [s] using hpc_old₃
      have hpc_inv0 : PcState.Invariant Γ s.self s.common_fund s.amount tr s.ps hcfv_s pc := by
        rw [heq_pc] at hpc_old_s
        simpa using hpc_old_s
      exact ⟨hcfv_s, hpc_inv0⟩
    rcases hpc_inv_ex with ⟨hcfv_s, hpc_inv⟩
    cases h_pc_complete
    rename_i pcself pcbalance pcself_rk pc_other_rk pc_other_hrk pc_signed pc_i
    cases hpc_inv with
    | All i_inv balance_inv self_rk_inv hhash hvp_ork hrec_inv =>
    let pc_full : PcState :=
      { self := s.self, balance := pcbalance, self_rk := pcself_rk,
        other_rk := some pc_other_rk, other_hrk := some pc_other_hrk,
        valid_sign_stripped := some pc_signed, i := pc_i }
    have hbalance_eq : pcbalance = balance := by simpa using hbalance
    have hpc_other_rk_eq : pc_other_rk = rk := by simpa using h_pc_other_rk
    have hother_hrk : pc_other_hrk = base_hrk := by
      apply BytesEq.NonFail.ext
      simpa [base_hrk, rk_hash, hpc_other_rk_eq] using hhash.symm
    have hmem : tx ∈ punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc_full := by
      simp [punishable_transactions, get_punish_data, pc_full, -instInhabitedPcState]
      constructor
      · rwa [Blockchain.mem_alt_def] at hin_tx
      constructor
      · refine ⟨(), ?_⟩
        rw [List.guard_def]
        rw [hcommon_fund_s]
        unfold Transaction.spends at h_spent
        exact h_spent
      · refine ⟨(), ?_⟩
        rw [List.guard_def]
        rw [hother_hrk, hbalance_eq]
        rw [hps_s, hself_s, hcommon_fund_s]
        simpa [base_hrk] using hout_base
    have hnonempty : punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc_full ≠ [] := by
      intro hnil
      rw [hnil] at hmem
      cases hmem
    rw [List.neq_nil_is_cons] at hnonempty
    obtain ⟨ptx, tl, heq_list⟩ := hnonempty
    exists pc_full, ptx
    have hmem_ptx : ptx ∈ punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc_full := by
      rw [heq_list]
      simp
    -- `pc_full` is complete by construction (all optional fields are `some _`).
    have hpc_full_complete : pc_full.IsComplete := PcState.IsComplete.intro
    and_intros
    · simpa [s, pc_full] using heq_pc
    · exact hpc_full_complete
    · simpa [pc_full] using h_pc_other_rk
    · rw [heq_list, List.head?_cons]
    · exact punishable_transactions_toLocalVout_valid (b := tr.get_blockchain) hv₂
        (ps := s.ps) (self := s.self) (common_fund := s.common_fund)
        (pc := pc_full) (ptx := ptx) hpc_full_complete hmem_ptx
    · have hout := punishable_transactions.mem_outputs_complete
        (self := s.self) (ps := s.ps) (b := tr.get_blockchain)
        (common_fund := s.common_fund) (balance := pcbalance)
        (self_rk := pcself_rk) (rk := pc_other_rk)
        (other_hrk := pc_other_hrk) (signed := pc_signed) (i := pc_i)
        (tx := ptx) hmem_ptx
      rw [hother_hrk] at hout
      simpa [pc_full, base_hrk] using hout





  abbrev punish.sound'_strong_out (ps:×× ℙ) (common_fund) := ∃ rk tx ptx self balance,
        (.PostDefended common_fund rk tx ∈' tr') ∧
        ptx ∈ tr.get_blockchain ∧
        tx.ninputs = 1 ∧
        (∃ hfirst : 0 < tx.inputs.val.length,
          (tx.inputs.val[0]'hfirst).outptr = ptx.mk_ptr self.toLocalVout) ∧
        ptx.outputs.val =
          (mk_base_transaction ps.vk self common_fund balance (rk_hash rk)).outputs.val ∧
        (∃ h₀ hptr, .Defended rk (tx.strip tr.get_blockchain 0 h₀ hptr) ∈' tr')

  theorem punish.sound'_strong
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
      punish.sound'_strong_out tr tr' ps common_fund
        := by
    have hspent_or := CommonFund.exists_spent_by_hrk
      (tr := tr) (ps := ps) (common_fund := common_fund) hv₁ hv₂ hcfv hcf hspent
    cases hspent_or with
    | inr hcorr => tauto
    | inl hspent_exists =>
    obtain ⟨hrk, self, balance, hspent_hrk⟩ := hspent_exists
    obtain ⟨rk, i, hhrk, hold⟩ := h_old hrk self balance hspent_hrk
    have hspent_hash :
        CommonFund.spent_by_hrk (tr.get_blockchain) ps common_fund hv₂ hcfv self (rk_hash rk) balance := by
      simpa [hhrk] using hspent_hrk
    let evs : Evs := .Old {ps, self, common_fund, i, rk, balance}
    let s := evs.get_state tr
    obtain ⟨pc_state, hstate, heq_pc_state, hready_state, hrk_state⟩ :=
      punish.get_state.correct tr hv₁ hold
    obtain ⟨pc, ptx, hpc_old, hready, hrk_pc, hhead, hptr, hptx_outputs_s⟩ :=
      punish_CommonFund_spent_by_hrk_strong_enough
        (tr := tr) (ps := ps) (common_fund := common_fund)
        (self := self) (rk := rk) (balance := balance) (i := i)
        hv₁ hv₂ hcfv hspent_hash hold
    obtain ⟨pc_oldv, hps, hself, hcf, hpc_old_fields, hbal_oldv⟩ :=
      punish.get_state.fields tr hv₁ hold
    have hs_ps : s.ps = ps := hps
    have hs_self : s.self = self := hself
    have hs_cf : s.common_fund = common_fund := hcf
    have hpc_balance : pc.balance = balance := by
      have hpc_eq : pc = pc_oldv := by grind
      cases hpc_eq
      exact hbal_oldv
    have hhead' : ∃ ptx,
        (punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc).head? = some ptx ∧
        (ptx.mk_ptr s.self.toLocalVout).valid (tr.get_blockchain) := ⟨ptx, hhead, hptr⟩
    let msg : 𝐵 Unit Nonce :=
      serialize (β := WithBlockchain Unit) {blockchain := tr.get_blockchain, msg := ()}
    have hselect : Blockchain.Liveness.Select DefenseSelector
        (punish noutputs outputs) tr
        (Blockchain.get_blockchain_idx tr hmined) i msg (.Std s) := by
      refine ⟨?_, ?_, ?_⟩
      · aapply DefenseSelector.intro
      · simpa [msg] using Blockchain.get_blockchain_idx.sound (tr := tr) hmined
      · exact hstate
    obtain ⟨l₁, l₂, htr'⟩ := hl
      (Blockchain.get_blockchain_idx tr hmined) i msg (.Std s) (punish noutputs outputs)
      hgrow hselect hheight
    obtain ⟨tx, ptx_emit, hhead_emit, hpost_atom, hdef_atom, hninputs_tx, hinput_eq⟩ :=
      punish_emits_postdefended_strong
        (i := l₁.length + tr.length) (noutputs := noutputs) (outputs := outputs)
        (b := tr.get_blockchain) (s := s) (pc := pc) (rk := rk)
        hpc_old hready hrk_pc hhead'
    have hptx_emit_eq : ptx_emit = ptx := by
      rw [hhead] at hhead_emit
      cases hhead_emit
      rfl
    subst ptx_emit
    have hmem_ptx_list : ptx ∈ punishable_transactions s.self s.ps (tr.get_blockchain) s.common_fund pc := by
      rw [List.head?_eq_some_iff] at hhead
      rcases hhead with ⟨tl, hlist⟩
      rw [hlist]
      simp
    have hptx_mem : ptx ∈ tr.get_blockchain := by
      rw [Blockchain.mem_alt_def]
      exact punishable_transactions.mem_transactions (self := s.self) (ps := s.ps)
        (b := tr.get_blockchain) (common_fund := s.common_fund) (state := pc) hmem_ptx_list
    have hpost_tr' : .PostDefended common_fund rk tx ∈' tr' := by
      have hpost_cf : .PostDefended common_fund rk tx ∈'
          (punish noutputs outputs (l₁.length + tr.length) msg (.Std s)).as_list_including := by
        simpa [hs_cf] using hpost_atom
      rw [htr']
      simp [Atom.as_list_including] at hpost_cf ⊢
      tauto
    have hdef_tr' : ∃ h₀ hptr, .Defended rk (tx.strip tr.get_blockchain 0 h₀ hptr) ∈' tr' := by
      rcases hdef_atom with ⟨h₀, hptr0, hdef0⟩
      refine ⟨h₀, hptr0, ?_⟩
      rw [htr']
      simp [Atom.as_list_including] at hdef0 ⊢
      tauto
    have houtputs : ptx.outputs.val =
        (mk_base_transaction ps.vk self common_fund balance (rk_hash rk)).outputs.val := by
      rw [← hs_ps, ← hs_self, ← hs_cf, ← hpc_balance]
      exact hptx_outputs_s
    have hinput_eq' : ∃ hfirst : 0 < tx.inputs.val.length,
        (tx.inputs.val[0]'hfirst).outptr = ptx.mk_ptr self.toLocalVout := by
      simpa [hs_self] using hinput_eq
    exact ⟨rk, tx, ptx, self, balance, hpost_tr', hptx_mem, hninputs_tx,
      hinput_eq', houtputs, hdef_tr'⟩

  /-- A `PostDefended` punishment transaction is either already on chain, or it
  has been valid for long enough to invoke miner liveness, provided the race
  analysis premise `havailable` holds. -/
  lemma postdefended_onchain_or_validLongEnough
      {common_fund : Blockchain.Pointer Unit Nonce} {rk : 𝒃}
      {tx : Blockchain.Transaction Unit Nonce}
      (miner_time : ℕ)
      (hv_final : valid_trace Γ tr_final)
      (hpost : .PostDefended common_fund rk tx ∈' tr_final)
      (hheight : ∀ t,
        Blockchain.published_to_miners tr_final tx t →
          (tr_final.get_blockchain_at t).height + miner_time <
            tr_final.get_blockchain.height)
      (havailable : ∀ t,
        Blockchain.published_to_miners tr_final tx t →
          ∀ tr_mid : 𝑇 Unit Nonce,
            tr_final.rtake t ≤ tr_mid → tr_mid ≤ tr_final →
              tx ∈ tr_mid.get_blockchain ∨
                tx.all_input_spendable tr_mid.get_blockchain) :
      tx ∈ tr_final.get_blockchain ∨
        ∃ t, Blockchain.published_to_miners tr_final tx t ∧
          tx.ValidLongEnough (P2WSH Script) miner_time tr_final t := by
    have hpost_valid : event_preds.PostDefendedP tr_final common_fund rk tx :=
      event_preds.PostDefendedP.of_valid_trace Γ tr_final hv_final hpost
    cases hpost_valid with
    | @intro i hmsg hninputs _hinput_valid _hspends_common_fund _hdefend hvalid_if_spendable =>
        have hpub : Blockchain.published_to_miners tr_final tx i := by
          simpa [Blockchain.published_to_miners] using hmsg
        have hprefix_final : tr_final.rtake i ≤ tr_final := List.rtake_self _ _
        obtain ⟨tr_mid, hprefix_mid, hmid_final, hheight_low, hheight_high⟩ :=
          Blockchain.exists_trace_between_height_of_suffix
            (tr₀ := tr_final.rtake i) (tr_final := tr_final)
            hprefix_final (by simpa using hheight i hpub)
        have havailable_pub := havailable i hpub (tr_final.rtake i) (by rfl) hprefix_final
        cases havailable_pub with
        | inl htx_pub =>
            left
            exact Blockchain.tx_mem_monotone (tx := tx)
              (List.get_blockchain_monotone hprefix_final) htx_pub
        | inr hspendable_pub =>
            have havailable_mid := havailable i hpub tr_mid hprefix_mid hmid_final
            cases havailable_mid with
            | inl htx_mid =>
                left
                exact Blockchain.tx_mem_monotone (tx := tx)
                  (List.get_blockchain_monotone hmid_final) htx_mid
            | inr hspendable_mid =>
                right
                refine ⟨i, hpub, ?_⟩
                have hvalid_pub : tx.valid (tr_final.rtake i).get_blockchain (P2WSH Script) :=
                  hvalid_if_spendable hspendable_pub
                have hnonzero : tx.ninputs ≠ 0 := by
                  rw [hninputs]
                  omega
                have hvalid_mid : tx.valid tr_mid.get_blockchain (P2WSH Script) :=
                  Blockchain.Transaction.valid_of_prefix_of_spendable
                    (b := (tr_final.rtake i).get_blockchain)
                    (b' := tr_mid.get_blockchain) (tx := tx)
                    (List.get_blockchain_monotone hprefix_mid) hnonzero hvalid_pub hspendable_mid
                exact Blockchain.Transaction.ValidLongEnough.intro
                  (script_t := P2WSH Script) (n := miner_time)
                  (tr := tr_final) (t := i) (tx := tx)
                  tr_mid hmid_final hheight_low hheight_high hvalid_mid

  /-- Miner-liveness corollary of `postdefended_onchain_or_validLongEnough`. -/
  lemma postdefended_onchain_of_available
      {common_fund : Blockchain.Pointer Unit Nonce} {rk : 𝒃}
      {tx : Blockchain.Transaction Unit Nonce}
      (miner_time : ℕ)
      (hv_final : valid_trace Γ tr_final)
      (hpost : .PostDefended common_fund rk tx ∈' tr_final)
      (hheight : ∀ t,
        Blockchain.published_to_miners tr_final tx t →
          (tr_final.get_blockchain_at t).height + miner_time <
            tr_final.get_blockchain.height)
      (havailable : ∀ t,
        Blockchain.published_to_miners tr_final tx t →
          ∀ tr_mid : 𝑇 Unit Nonce,
            tr_final.rtake t ≤ tr_mid → tr_mid ≤ tr_final →
              tx ∈ tr_mid.get_blockchain ∨
                tx.all_input_spendable tr_mid.get_blockchain)
      (hminer : ∀ t tx,
        Blockchain.miner_liveness (P2WSH Script) Blockchain.published_to_miners
          miner_time tr_final t tx) :
      tx ∈ tr_final.get_blockchain := by
    have h := postdefended_onchain_or_validLongEnough
      (tr_final := tr_final) (common_fund := common_fund) (rk := rk) (tx := tx)
      miner_time hv_final hpost hheight havailable
    cases h with
    | inl htx => exact htx
    | inr hlong =>
        rcases hlong with ⟨t, hpub, hvlong⟩
        exact hminer t tx hpub hvlong

  lemma postdefended_self_witness
      {common_fund : Blockchain.Pointer Unit Nonce} {rk : 𝒃}
      {tx : Blockchain.Transaction Unit Nonce}
      (hv_final : valid_trace Γ tr_final)
      (hpost : .PostDefended common_fund rk tx ∈' tr_final)
      (htx : tx ∈ tr_final.get_blockchain) :
      ∃ tx', tx' ∈ tr_final.get_blockchain ∧
        ∃ h₁ h₂ h₃ h₄,
          tx.strip tr_final.get_blockchain 0 h₁ h₂ =
            tx'.strip tr_final.get_blockchain 0 h₃ h₄ := by
    have hpost_valid : event_preds.PostDefendedP tr_final common_fund rk tx :=
      event_preds.PostDefendedP.of_valid_trace Γ tr_final hv_final hpost
    cases hpost_valid with
    | @intro i _hmsg hninputs hinput_valid _hspends_common_fund _hdefend _hvalid =>
        refine ⟨tx, htx, ?_⟩
        have h₁ : 0 < tx.inputs.length := by
          simp [Vec.length, hninputs]
        have h₂ : (tx.inputs.val[0]'(by simpa using h₁)).outptr.valid tr_final.get_blockchain := by
          exact Blockchain.Pointer.valid_monotone
            (ptr := (tx.inputs.val[0]'(by simpa using h₁)).outptr)
            (List.get_blockchain_monotone (List.rtake_self tr_final i))
            (by simpa [hninputs] using hinput_valid)
        refine ⟨h₁, h₂, h₁, h₂, rfl⟩

  namespace List
    variable (tr:𝑇 Unit Nonce) (tx: Transaction Unit Nonce)
    def get_blockchain_at_tx  : 𝑇 Unit Nonce :=
      tr.get_tr_of_blockchain_size (tx.txid.get_block_idx tr.get_blockchain + 1)

    omit param in
    @[grind]
    lemma get_blockchain_at_tx_leq : tr.get_blockchain_at_tx tx <= tr := by
      exact List.get_tr_of_blockchain_size_le tr (tx.txid.get_block_idx tr.get_blockchain + 1)

    omit param in
    @[grind]
    lemma get_blockchain_at_tx_mem
        (hv : tr.get_blockchain.valid (P2WSH Script)) :
        tx ∈ (tr.get_blockchain_at_tx tx).get_blockchain ↔ tx ∈ tr.get_blockchain := by
      constructor
      · intro h
        exact Blockchain.tx_mem_monotone
          (tx := tx)
          (List.get_blockchain_monotone (List.get_blockchain_at_tx_leq tr tx)) h
      · intro htx
        let b : Blockchain Unit Nonce := tr.get_blockchain
        let tr₀ : 𝑇 Unit Nonce := tr.get_blockchain_at_tx tx
        let b₀ : Blockchain Unit Nonce := tr₀.get_blockchain
        have hb₀ : b₀ ≤ b := by
          dsimp [b, b₀, tr₀]
          exact List.get_blockchain_monotone (List.get_blockchain_at_tx_leq tr tx)
        have htxid_b : tx.txid.valid b := by
          dsimp [b]
          exact Blockchain.tx_mem_txid_valid (b := tr.get_blockchain) (tx := tx) htx
        have hidx_lt : tx.txid.get_block_idx b < b.height := by
          exact Blockchain.TXID.get_block_idx_le (b := b) (txid := tx.txid) htxid_b
        have hheight₀ : b₀.height = tx.txid.get_block_idx b + 1 := by
          dsimp [b₀, tr₀, b, List.get_blockchain_at_tx]
          exact List.get_tr_of_blockchain_size.height_leq tr
            (tx.txid.get_block_idx tr.get_blockchain + 1)
            (by simpa [b] using Nat.succ_le_of_lt hidx_lt)
        have htxid_b₀ : tx.txid.valid b₀ := by
          dsimp [Blockchain.TXID.valid]
          rw [Blockchain.txids_block_txids_mem_iff]
          let idx := tx.txid.get_block_idx b
          have hidx_lt_b₀_height : idx < b₀.height := by
            change idx < b₀.blocks.length
            dsimp [idx]
            rw [show b₀.blocks.length = tx.txid.get_block_idx b + 1 by simpa [Blockchain.height] using hheight₀]
            omega
          have hidx_lt_b₀ : idx < b₀.blocks.length := by
            simpa [Blockchain.height] using hidx_lt_b₀_height
          have hidx_mem_full : tx.txid ∈ (b.blocks[idx]'(by simpa [idx] using hidx_lt)).txids := by
            dsimp [idx]
            have hfind : (b.blocks.findIdx (fun bl => tx.txid ∈ bl.txids)) < b.blocks.length := by
              simpa [Blockchain.TXID.get_block_idx, Blockchain.height] using hidx_lt
            simpa using (List.findIdx_getElem (xs := b.blocks)
              (p := fun bl => tx.txid ∈ bl.txids) (w := hfind))
          refine ⟨b₀.blocks[idx]'hidx_lt_b₀, List.getElem_mem hidx_lt_b₀, ?_⟩
          have hblock_eq : b₀.blocks[idx]'hidx_lt_b₀ =
                b.blocks[idx]'(by simpa [idx] using hidx_lt) := by
            exact Blockchain.block_stable b₀ b idx hidx_lt_b₀_height hb₀
          rwa [hblock_eq]
        have hnodup_b : b.no_duplicates := by
          dsimp [b]
          exact Blockchain.valid_impl_no_duplicates (b := tr.get_blockchain)
            (script_t := P2WSH Script) hv
        have htx_get : b[tx.txid]'htxid_b = tx := hnodup_b tx (by simpa [b] using htx)
        have hstable : b₀[tx.txid]'htxid_b₀ = b[tx.txid]'htxid_b := by
          exact Blockchain.getElem_stable (b := b₀) (b' := b)
            (txid := tx.txid) hb₀ htxid_b₀
        have hmem_get : b₀[tx.txid]'htxid_b₀ ∈ b₀ := by
          exact Blockchain.getElem_mem (b := b₀) (txid := tx.txid) (h := htxid_b₀)
        rwa [hstable, htx_get] at hmem_get
  end List

  section
    variable
      {tr tr_final : 𝑇 Unit Nonce}
      (punish_time miner_time : ℕ)

  omit param in
  lemma exists_cheating_tr {tx}
    (hgrow : tr ≤ tr_final)
    (hmining : continuous_mining tr_final)
    (hheight_lt : tr.get_blockchain.height < tr_final.get_blockchain.height) :
    ∃ tr₀, tr.get_blockchain_at_tx tx ≤ tr₀ ∧ tr₀ ≤ tr_final ∧ Blockchain.mined tr₀ ∧ (tr.get_blockchain_at_tx tx).get_blockchain = tr₀.get_blockchain := by
    aapply hmining;
    · trans
      aapply List.get_blockchain_at_tx_leq
      assumption
    · rfl
    · have hle : (tr.get_blockchain_at_tx tx).get_blockchain ≤ tr_final.get_blockchain := by
        exact List.get_blockchain_monotone
          (le_trans (List.get_blockchain_at_tx_leq tr tx) hgrow)
      have hheight_cheat_le : (tr.get_blockchain_at_tx tx).get_blockchain.height ≤ tr.get_blockchain.height := by
        exact Blockchain.height_monotone
          (List.get_blockchain_monotone (List.get_blockchain_at_tx_leq tr tx))
      exact ⟨hle, by
        intro hrev
        have hh := Blockchain.height_monotone hrev
        omega⟩

  variable
    (cheating_tx : Transaction Unit Nonce)
    (tr_cheating : 𝑇 Unit Nonce)

  lemma exists_defending_tr
    (htime_budget : punish_time + miner_time < ScriptParam.toSelfDelay)
    (hgrow : tr ≤ tr_final)
    (hheight_final : (List.get_blockchain tr).height + ScriptParam.toSelfDelay ≤ (List.get_blockchain tr_final).height)
    (hmining : continuous_mining tr_final)
    (htr₀gew : List.get_blockchain_at_tx tr cheating_tx ≤ tr_cheating)
    (htr₀eq : List.get_blockchain (List.get_blockchain_at_tx tr cheating_tx) = List.get_blockchain tr_cheating)
    :
    let tr_defend' := List.get_tr_of_blockchain_size tr_final ((List.get_blockchain tr_cheating).height + punish_time)
     ∃ tr₀, tr_defend' ≤ tr₀ ∧ tr₀ ≤ tr_final ∧ mined tr₀ ∧ tr_defend'.get_blockchain = tr₀.get_blockchain := by
      let tr_defend' := List.get_tr_of_blockchain_size tr_final ((List.get_blockchain tr_cheating).height + punish_time)
      apply hmining
      · aapply List.get_tr_of_blockchain_size_le
      · rfl
      · have hle : tr_defend'.get_blockchain ≤ tr_final.get_blockchain := by
          aapply List.get_blockchain_monotone
          aapply List.get_tr_of_blockchain_size_le tr_final
        have hcheat_height_le_tr : tr_cheating.get_blockchain.height ≤ tr.get_blockchain.height := by
          rw [← htr₀eq]
          apply Blockchain.height_monotone
          aapply List.get_blockchain_monotone
          aapply List.get_blockchain_at_tx_leq
        have hheight_def : tr_defend'.get_blockchain.height = tr_cheating.get_blockchain.height + punish_time := by
          dsimp [tr_defend']
          apply List.get_tr_of_blockchain_size.height_leq tr_final (tr_cheating.get_blockchain.height + punish_time)
          omega
        constructor
        · exact hle
        · grind
  end


lemma liveness_no_race
  (tr tr_final : 𝑇 Unit Nonce)
  (common_fund : Pointer Unit Nonce)
  (punish_time miner_time : ℕ)
  (htime_budget : punish_time + miner_time < ScriptParam.toSelfDelay)
  (hheight_final : (List.get_blockchain tr).height + ScriptParam.toSelfDelay ≤ (List.get_blockchain tr_final).height)
  (hv₁ : valid_trace Γ tr_final)
  (hv₂ : (List.get_blockchain tr_final).valid (P2WSH _root_.Script))
  (hminer : ∀ (t : 𝕥) (tx : Transaction Unit Nonce), miner_liveness (P2WSH _root_.Script) published_to_miners miner_time tr_final t tx)
  (cheating_tx : Transaction Unit Nonce)
  (tr_cheating : 𝑇 Unit Nonce)
  (tr_defend : List (𝑇𝐸 Unit Nonce))
  -- (htr₃gew : tr_defend' ≤ tr_defend)
  (htr₃leq : tr_defend ≤ tr_final)
  (rk : 𝑩 Unit Nonce)
  (tx_defend  : Transaction Unit Nonce)
  (hev : Evs.PostDefended common_fund rk tx_defend ∈' tr_defend)
  (htx_input0 : 0 < tx_defend.inputs.val.length)
  (i : 𝕥)
  (hsm : Trace.IsMessageAt tr_defend i (serialize (β := ToBlockchain) { tx := tx_defend }))
  (hninputs : tx_defend.ninputs = 1)
  (hinput_valid : Pointer.valid (tr_defend.rtake i).get_blockchain (tx_defend.inputs.val[0]'htx_input0).outptr)
  (hv : Transaction.all_input_spendable (tr_defend.rtake i).get_blockchain tx_defend → Transaction.valid (tr_defend.rtake i).get_blockchain tx_defend (P2WSH _root_.Script))
  (hpub_final : tr_defend.rtake i ≤ tr_final)
  (hheight_cheat_le_tr : (List.get_blockchain tr_cheating).height ≤ (List.get_blockchain tr).height)
  (hdef_height : tr_defend.get_blockchain.height = (List.get_blockchain tr_cheating).height + punish_time)
  (hpub_height_le_def : (tr_defend.rtake i).get_blockchain.height ≤ tr_defend.get_blockchain.height)
  (hdeadline_height_le_final : (tr_defend.rtake i).get_blockchain.height + miner_time ≤ (List.get_blockchain tr_final).height)
  (ho₁ : tr_defend.rtake i ≤ (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)))
  (ho₂ : (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)).get_blockchain.height = (tr_defend.rtake i).get_blockchain.height + miner_time)
  (hspend : Transaction.all_input_spendable (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)).get_blockchain tx_defend) :
  ∃ rk tx tx',
    (Evs.PostDefended common_fund rk tx ∈' tr_final)
      ∧ tx' ∈ List.get_blockchain tr_final
      ∧ ∃ h₁ h₂ h₃ h₄, Transaction.strip (List.get_blockchain tr_final) tx 0 h₁ h₂ = Transaction.strip (List.get_blockchain tr_final) tx' 0 h₃ h₄ := by
  let tr_cheating' : 𝑇 Unit Nonce := List.get_blockchain_at_tx tr cheating_tx
  let tr_defend' : List (𝑇𝐸 Unit Nonce) := List.get_tr_of_blockchain_size tr_final ((List.get_blockchain tr_cheating).height + punish_time)
  let tr_final₀ : List (𝑇𝐸 Unit Nonce) := List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)
  have hv_pub_chain : (tr_defend.rtake i).get_blockchain.valid (P2WSH Script) := by
    exact Blockchain.valid_antitone (script_t := P2WSH Script)
      (a := (tr_defend.rtake i).get_blockchain) (b := tr_final.get_blockchain)
      (List.get_blockchain_monotone hpub_final) hv₂
  let ptr0 : Blockchain.Pointer Unit Nonce :=
    (tx_defend.inputs.val[0]'(by rw [tx_defend.inputs.property, hninputs]; omega)).outptr
  -- `tx_defend` has a single input, so its input-pointer list is exactly `[ptr0]`.
  have hinput_ptrs_tx_defend : tx_defend.input_ptrs = [ptr0] := by
    rw [Blockchain.Transaction.input_ptrs_singleton_of_ninputs_eq_one tx_defend hninputs]
  have hptr0_valid_pub : ptr0.valid (tr_defend.rtake i).get_blockchain := by
    simpa [ptr0] using hinput_valid
  have hptr0_spend_deadline : ptr0 ∈ tr_final₀.get_blockchain.spendable_ptrs := by
    have hsp := hspend
    unfold Blockchain.Transaction.all_input_spendable at hsp
    rw [hinput_ptrs_tx_defend] at hsp
    simpa [ptr0] using hsp
  have hptr0_not_spent_deadline : ptr0 ∉ tr_final₀.get_blockchain.input_ptrs := by
    exact Blockchain.Pointer.not_spent_of_mem_spendable_ptrs hptr0_spend_deadline
  have hptr0_not_spent_pub : ptr0 ∉ (tr_defend.rtake i).get_blockchain.input_ptrs := by
    intro hspent_pub
    apply hptr0_not_spent_deadline
    rw [Blockchain.input_ptrs_mem] at hspent_pub ⊢
    rcases hspent_pub with ⟨txs, htxs, hptrs⟩
    exact ⟨txs, Blockchain.tx_mem_monotone
      (tx := txs) (List.get_blockchain_monotone ho₁) htxs, hptrs⟩
  have hptr0_unique_pub : ptr0.txid.unique (tr_defend.rtake i).get_blockchain := by
    exact Blockchain.no_duplicates_id_unique _ _
      (Blockchain.valid_impl_no_duplicates
        (b := (tr_defend.rtake i).get_blockchain)
        (script_t := P2WSH Script) hv_pub_chain)
  have hptr0_spend_pub : ptr0 ∈ (tr_defend.rtake i).get_blockchain.spendable_ptrs := by
    exact Blockchain.Pointer.spendable_of_valid_not_spent
      hptr0_valid_pub hptr0_unique_pub hptr0_not_spent_pub
  have hspend_pub : tx_defend.all_input_spendable (tr_defend.rtake i).get_blockchain := by
    exact Blockchain.Transaction.all_input_spendable_of_first tx_defend
      (tr_defend.rtake i).get_blockchain hninputs
      (by rw [tx_defend.inputs.property, hninputs]; omega)
      (by simpa [ptr0] using hptr0_spend_pub)
  have hv_pub : tx_defend.valid (tr_defend.rtake i).get_blockchain (P2WSH Script) := by
    exact hv hspend_pub
  have hv_deadline : tx_defend.valid tr_final₀.get_blockchain (P2WSH Script) := by
    exact Blockchain.Transaction.valid_of_prefix_of_spendable
      (b := (tr_defend.rtake i).get_blockchain)
      (b' := tr_final₀.get_blockchain) (tx := tx_defend)
      (List.get_blockchain_monotone ho₁)
      (by rw [hninputs]; omega) hv_pub hspend
  have hpublished_final : Blockchain.published_to_miners tr_final tx_defend i := by
    simpa [Blockchain.published_to_miners] using
      (Trace.IsMessageAt.monotone htr₃leq hsm)
  have hrtake_eq : tr_defend.rtake i = tr_final.rtake i := by
    cases hsm with
    | intro hl _ => exact List.rtake_suffix tr_defend tr_final i htr₃leq (Nat.le_of_lt hl)
  have htx_onchain : tx_defend ∈ tr_final.get_blockchain := by
    apply hminer i tx_defend
    · simpa [Blockchain.published_to_miners] using hpublished_final
    · refine Blockchain.Transaction.ValidLongEnough.intro
        (script_t := P2WSH Script) (n := miner_time)
        (tr := tr_final) (t := i) (tx := tx_defend)
        tr_final₀ ?_ ?_ ?_ hv_deadline
      · exact List.get_tr_of_blockchain_size_le tr_final
          ((tr_defend.rtake i).get_blockchain.height + miner_time)
      · change (tr_final.rtake i).get_blockchain.height + miner_time ≤ tr_final₀.get_blockchain.height
        rw [← congrArg (fun tr : 𝑇 Unit Nonce => tr.get_blockchain.height) hrtake_eq, ho₂]
      · rw [ho₂]
        rw [hdef_height] at hpub_height_le_def
        have hstrict : tr_cheating.get_blockchain.height + punish_time + miner_time <
            tr_cheating.get_blockchain.height + param.toSelfDelay := by
          omega
        omega
  obtain ⟨txw, htxw, heqw⟩ := postdefended_self_witness
    (tr_final := tr_final) (common_fund := common_fund) (rk := rk)
    (tx := tx_defend) hv₁ (List.IsSuffix.mem hev htr₃leq) htx_onchain
  exact ⟨rk, tx_defend, txw, List.IsSuffix.mem hev htr₃leq, htxw, heqw⟩


lemma liveness_race
  (tr tr_final : 𝑇 Unit Nonce)
  (ps : ×× ℙ)
  (common_fund : Pointer Unit Nonce)
  (punish_time miner_time : ℕ)
  (htime_budget : punish_time + miner_time < ScriptParam.toSelfDelay)
  (hv₁ : valid_trace Γ tr_final)
  (hv₂ : (List.get_blockchain tr_final).valid (P2WSH _root_.Script))
  (hno_collision : ∀ (rk : 𝑩 Unit Nonce) (stx stx' : StripedTransaction Unit Nonce), (Evs.Defended rk stx ∈' tr_final) → (Evs.Defended rk stx' ∈' tr_final) → stx' = stx)
  (hv₂_tr : (List.get_blockchain tr).valid (P2WSH _root_.Script))
  (hnot_corrupta : TraceEvent.Corrupt ps.a ∉ tr_final)
  (hnot_corruptb : TraceEvent.Corrupt ps.b ∉ tr_final)
  (cheating_tx : Transaction Unit Nonce)
  (hin : cheating_tx ∈ List.get_blockchain tr)
  (hin' : common_fund ∈ cheating_tx.input_ptrs)
  (tr_cheating : 𝑇 Unit Nonce)
  (htr₀leq : tr_cheating ≤ tr_final)
  (htr₀eq : List.get_blockchain (List.get_blockchain_at_tx tr cheating_tx) = List.get_blockchain tr_cheating)
  (tr_defend : List (𝑇𝐸 Unit Nonce))
  (htr₃leq : tr_defend ≤ tr_final)
  (rk : 𝑩 Unit Nonce)
  (tx_defend ptx_cheat : Transaction Unit Nonce)
  (self_def : AOrB)
  (balance_def : ×× ₿)
  (hptx_cheat_mem_ch : ptx_cheat ∈ List.get_blockchain tr_cheating)
  (htx_input0: 0 < tx_defend.inputs.val.length )
  (htx_input_eq_strong : (tx_defend.inputs.val[0]'htx_input0).outptr = ptx_cheat.mk_ptr self_def.toLocalVout)
  (hptx_outputs_strong : ptx_cheat.outputs.val = (mk_base_transaction ps.vk self_def common_fund balance_def (rk_hash rk)).outputs.val)
  (hdef_strong : ∃ h₀ hptr, Evs.Defended rk (Transaction.strip (List.get_blockchain tr_cheating) tx_defend 0 h₀ hptr) ∈' tr_defend)
  (i : 𝕥)
  (hninputs : tx_defend.ninputs = 1)
  (hinput_valid : Pointer.valid (tr_defend.rtake i).get_blockchain (tx_defend.inputs.val[0]'htx_input0).outptr)
  (ptr_cheat : Pointer Unit Nonce)
  (hcspendt_cheat : tx_defend.spends ptr_cheat)
  (hptr_cheat_txid_pub : TXID.valid (tr_defend.rtake i).get_blockchain ptr_cheat.txid)
  (hspends : (tr_defend.rtake i).get_blockchain[ptr_cheat.txid].spends common_fund)
  (stx : StripedTransaction Unit Nonce)
  (hstx_in : Evs.Defended rk stx ∈' tr_defend)
  (hstx_h0 : 0 < tx_defend.inputs.length)
  (hstx_hptr : Pointer.valid (tr_defend.rtake i).get_blockchain (tx_defend.inputs.val[0]'htx_input0).outptr)
  (hstx_eq : stx = Transaction.strip (tr_defend.rtake i).get_blockchain tx_defend 0 hstx_h0 hstx_hptr)
  (hpub_final : tr_defend.rtake i ≤ tr_final)
  (hdef_height : tr_defend.get_blockchain.height = (List.get_blockchain tr_cheating).height + punish_time)
  (ho₁ : tr_defend.rtake i ≤ (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)))
  (ho₂ : (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)).get_blockchain.height = (tr_defend.rtake i).get_blockchain.height + miner_time)
  (hspend : ¬Transaction.all_input_spendable (List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)).get_blockchain tx_defend) :
  ∃ tx' ∈ List.get_blockchain tr_final, ∃ h₁ h₂ h₃ h₄,
    Transaction.strip (List.get_blockchain tr_final) tx_defend 0 h₁ h₂ = Transaction.strip (List.get_blockchain tr_final) tx' 0 h₃ h₄ := by
  let tr_cheating' : 𝑇 Unit Nonce := List.get_blockchain_at_tx tr cheating_tx
  let tr_final₀ : List (𝑇𝐸 Unit Nonce) := List.get_tr_of_blockchain_size tr_final ((tr_defend.rtake i).get_blockchain.height + miner_time)
  let bpub := (tr_defend.rtake i).get_blockchain
  let bdead := tr_final₀.get_blockchain
  let bfin := tr_final.get_blockchain
  let ptr0 : Blockchain.Pointer Unit Nonce :=
    (tx_defend.inputs.val[0]'(by rw [tx_defend.inputs.property, hninputs]; omega)).outptr
  -- `tx_defend` has a single input, so its input-pointer list is exactly `[ptr0]`.
  have hinput_ptrs_tx_defend : tx_defend.input_ptrs = [ptr0] := by
    rw [Blockchain.Transaction.input_ptrs_singleton_of_ninputs_eq_one tx_defend hninputs]
  have hptr0_valid_pub : ptr0.valid bpub := by
    simpa [bpub, ptr0] using hinput_valid
  have hpub_dead_bc : bpub ≤ bdead := by
    exact List.get_blockchain_monotone ho₁
  have hdead_fin : bdead ≤ bfin := by
    dsimp [bdead, bfin, tr_final₀]
    exact List.get_blockchain_monotone
      (List.get_tr_of_blockchain_size_le tr_final
        ((tr_defend.rtake i).get_blockchain.height + miner_time))
  have hptr0_valid_dead : ptr0.valid bdead :=
    Blockchain.Pointer.valid_monotone (ptr := ptr0) hpub_dead_bc hptr0_valid_pub
  have hv_dead_chain : bdead.valid (P2WSH Script) := by
    exact Blockchain.valid_antitone (script_t := P2WSH Script)
      (a := bdead) (b := bfin) hdead_fin hv₂
  have hptr0_unique_dead : ptr0.txid.unique bdead := by
    exact Blockchain.no_duplicates_id_unique _ _
      (Blockchain.valid_impl_no_duplicates
        (b := bdead) (script_t := P2WSH Script) hv_dead_chain)
  have hptr0_not_spendable_dead : ptr0 ∉ bdead.spendable_ptrs := by
    intro hptr_sp
    apply hspend
    unfold Blockchain.Transaction.all_input_spendable
    rw [hinput_ptrs_tx_defend]
    simpa [ptr0]
  have hptr0_spent_dead : ptr0 ∈ bdead.input_ptrs := by
    exact Blockchain.Pointer.spent_of_valid_unique_not_spendable
      hptr0_valid_dead hptr0_unique_dead hptr0_not_spendable_dead
  obtain ⟨tx', htx'_dead, htx'_spends_ptr0⟩ := Blockchain.Pointer.spent.of_tx bdead hptr0_spent_dead
  have htx'_fin : tx' ∈ bfin := Blockchain.tx_mem_monotone (tx := tx') hdead_fin htx'_dead
  refine ⟨tx', htx'_fin, ?_⟩
  have hbpub_fin : bpub ≤ bfin := by
    exact List.get_blockchain_monotone hpub_final
  have hprefix_pub_fin : bpub.transactions <+: bfin.transactions :=
    Blockchain.transactions_prefix_of_le hbpub_fin
  have hprefix_dead_fin : bdead.transactions <+: bfin.transactions :=
    Blockchain.transactions_prefix_of_le hdead_fin
  have hptr0_ptx : ptr0 = ptx_cheat.mk_ptr self_def.toLocalVout := by
    simpa [ptr0] using htx_input_eq_strong
  have hptr_cheat_eq_ptr0 : ptr_cheat = ptr0 := by
    have hc : ptr_cheat ∈ tx_defend.input_ptrs := by
      simpa [Blockchain.Transaction.spends] using hcspendt_cheat
    rw [hinput_ptrs_tx_defend] at hc
    simpa [ptr0] using hc
  have hptr0_txid_pub : ptr0.txid.valid bpub := by
    simpa [bpub, hptr_cheat_eq_ptr0] using hptr_cheat_txid_pub
  have hparent_pub_spends :
      (bpub[ptr0.txid]'hptr0_txid_pub).spends common_fund := by
    simpa [bpub, hptr_cheat_eq_ptr0, hptr0_txid_pub] using hspends
  have hptx_txid : ptx_cheat.txid = ptr0.txid := by
    rw [hptr0_ptx]
    simp [Blockchain.Transaction.mk_ptr]
  have hptx_fin : ptx_cheat ∈ bfin := by
    exact Blockchain.tx_mem_monotone (tx := ptx_cheat)
      (List.get_blockchain_monotone htr₀leq) hptx_cheat_mem_ch
  have hparent_eq_ptx :
      bpub[ptr0.txid]'hptr0_txid_pub = ptx_cheat := by
    have huniq_fin : ptr0.txid.unique bfin := by
      exact Blockchain.no_duplicates_id_unique _ _
        (Blockchain.valid_impl_no_duplicates
          (b := bfin) (script_t := P2WSH Script) hv₂)
    apply huniq_fin
    · exact Blockchain.tx_mem_monotone (tx := bpub[ptr0.txid]'hptr0_txid_pub)
        hbpub_fin (Blockchain.getElem_mem (b := bpub) (txid := ptr0.txid)
          (h := hptr0_txid_pub))
    · exact hptx_fin
    · constructor
      · exact Blockchain.getElem_txid_txid (b := bpub) (txid := ptr0.txid)
          (h := hptr0_txid_pub)
      · exact hptx_txid
  have hptx_spends_cf : ptx_cheat.spends common_fund := by
    rw [← hparent_eq_ptx]
    exact hparent_pub_spends
  have htx_cheat' : cheating_tx ∈ tr_cheating'.get_blockchain := by
    exact (List.get_blockchain_at_tx_mem tr cheating_tx hv₂_tr).2 hin
  have htx_cheat_ch : cheating_tx ∈ tr_cheating.get_blockchain := by
    rwa [htr₀eq] at htx_cheat'
  have hv2_ch : tr_cheating.get_blockchain.valid (P2WSH Script) := by
    exact Blockchain.valid_antitone (script_t := P2WSH Script)
      (a := tr_cheating.get_blockchain) (b := bfin)
      (List.get_blockchain_monotone htr₀leq) hv₂
  have hcheat_spends_cf : cheating_tx.spends common_fund := by
    simpa [Blockchain.Transaction.spends] using hin'
  have hptx_eq_cheat : ptx_cheat = cheating_tx := by
    exact Blockchain.Transaction.no_double_spends
      (script_t := P2WSH Script) (b := tr_cheating.get_blockchain)
      (ptr := common_fund) ptx_cheat cheating_tx hv2_ch
      hptx_cheat_mem_ch htx_cheat_ch hptx_spends_cf hcheat_spends_cf
  have hptr0_valid_ch : ptr0.valid tr_cheating.get_blockchain := by
    rcases hdef_strong with ⟨h0, hptr, _⟩
    simpa [ptr0] using hptr
  have htip : ptr0.txid.get_block_idx tr_cheating.get_blockchain + 1 =
      tr_cheating.get_blockchain.height := by
    let btr := tr.get_blockchain
    have htxid_b : cheating_tx.txid.valid btr := by
      exact Blockchain.tx_mem_txid_valid (b := tr.get_blockchain) (tx := cheating_tx) hin
    have hidx_lt : cheating_tx.txid.get_block_idx btr < btr.height := by
      exact Blockchain.TXID.get_block_idx_le (b := btr) (txid := cheating_tx.txid) htxid_b
    have hheight_cheat' : tr_cheating'.get_blockchain.height =
        cheating_tx.txid.get_block_idx tr.get_blockchain + 1 := by
      dsimp [tr_cheating', List.get_blockchain_at_tx]
      exact List.get_tr_of_blockchain_size.height_leq tr
        (cheating_tx.txid.get_block_idx tr.get_blockchain + 1)
        (by simpa [btr] using Nat.succ_le_of_lt hidx_lt)
    have hb_ch_tr : tr_cheating.get_blockchain ≤ tr.get_blockchain := by
      rw [← htr₀eq]
      exact List.get_blockchain_monotone (List.get_blockchain_at_tx_leq tr cheating_tx)
    have hidx_stable : cheating_tx.txid.get_block_idx tr_cheating.get_blockchain =
        cheating_tx.txid.get_block_idx tr.get_blockchain := by
      exact Blockchain.TXID.get_block_idx_stable
        (b := tr_cheating.get_blockchain) (b' := tr.get_blockchain)
        (txid := cheating_tx.txid)
        (Blockchain.tx_mem_txid_valid (b := tr_cheating.get_blockchain)
          (tx := cheating_tx) htx_cheat_ch) hb_ch_tr
    have hptr0_txid : ptr0.txid = cheating_tx.txid := by
      rw [hptr0_ptx, hptx_eq_cheat]
      simp [Blockchain.Transaction.mk_ptr]
    calc
      ptr0.txid.get_block_idx tr_cheating.get_blockchain + 1
          = cheating_tx.txid.get_block_idx tr_cheating.get_blockchain + 1 := by rw [hptr0_txid]
      _ = cheating_tx.txid.get_block_idx tr.get_blockchain + 1 := by rw [hidx_stable]
      _ = tr_cheating'.get_blockchain.height := hheight_cheat'.symm
      _ = tr_cheating.get_blockchain.height := by rw [htr₀eq]
  have htx'_spends_map : ptr0 ∈ List.map Blockchain.Input.outptr tx'.inputs.val := by
    simpa [Blockchain.Transaction.input_ptrs] using htx'_spends_ptr0
  rw [List.mem_map] at htx'_spends_map
  rcases htx'_spends_map with ⟨inputj, hinputj_mem, hinputj_ptr⟩
  let j := tx'.inputs.val.idxOf inputj
  have hj : j < tx'.inputs.val.length := List.idxOf_lt_length_iff.mpr hinputj_mem
  have hgetj : tx'.inputs.val[j]'hj = inputj := List.getElem_idxOf hj
  have hinputj_ptr0 : (tx'.inputs.val[j]'hj).outptr = ptr0 := by
    rw [hgetj]
    exact hinputj_ptr
  let bsub := tx'.get_sub_blockchain bdead
  have htx'_valid_sub : tx'.valid bsub (P2WSH Script) := by
    exact hv_dead_chain tx' htx'_dead
  have hptrj_sub : (tx'.inputs.val[j]'(by simpa using hj)).outptr.valid bsub := by
    exact Blockchain.Transaction.valid_ptr_valid'
      (b := bsub) (tx := tx') (script_t := P2WSH Script)
      htx'_valid_sub (by simpa using hj)
  have hptr0_sub : ptr0.valid bsub := by
    simpa [hinputj_ptr0] using hptrj_sub
  let tl : ToLocal := {
    pk_regular := ps.vk[self_def],
    pk_punish := ps.vk[self_def.other],
    hrk_punish := rk_hash rk,
    to_self_delay := param.toSelfDelay }
  let amount := (bsub.get_output ptr0 hptr0_sub).amount
  have houtput_tl : bsub.get_output (tx'.inputs.val[j]'(by simpa using hj)).outptr hptrj_sub =
      P2WSH.mkOutput (S:=Script) amount (Script.ToLocal tl) := by
    have hptr_ptx_sub : (ptx_cheat.mk_ptr self_def.toLocalVout).valid bsub := by
      simpa [hptr0_ptx] using hptr0_sub
    have hout := toLocal_output_of_base_outputs
      (b := bsub) (ps := ps) (self := self_def)
      (common_fund := common_fund) (balance := balance_def) (ohrk := rk_hash rk)
      (ptx := ptx_cheat) hptx_outputs_strong hptr_ptx_sub
    simpa [tl, amount, hinputj_ptr0, hptr0_ptx] using hout
  have hrel : bsub.height -
        ((tx'.inputs.val[j]'(by simpa using hj)).outptr.txid.get_block_idx bsub + 1) <
      tl.to_self_delay := by
    have hidx_lt_sub : (tx'.inputs.val[j]'(by simpa using hj)).outptr.txid.get_block_idx bsub < bsub.height := by
      exact Blockchain.TXID.get_block_idx_le (b := bsub)
        (txid := (tx'.inputs.val[j]'(by simpa using hj)).outptr.txid) hptrj_sub.txid_valid
    have hheight_sub : bsub.height = 1 := by
      simp [bsub, Blockchain.height, Blockchain.Transaction.get_sub_blockchain]
    have hidx_zero : (tx'.inputs.val[j]'(by simpa using hj)).outptr.txid.get_block_idx bsub = 0 := by omega
    have hdelay_pos : 0 < param.toSelfDelay := by omega
    simp [tl, hheight_sub, hidx_zero]
    exact hdelay_pos
  have hnot_corrupt_self : TraceEvent.Corrupt ps[self_def.other] ∉ tr_final := by
    cases self_def
    · simpa using hnot_corruptb
    · simpa using hnot_corrupta
  obtain ⟨stx', hdef_tx', hstrip_tx'⟩ := toLocal_valid_input_defended
    (tr_final := tr_final) (bfull := bdead) (tx := tx') (i := j)
    hv₁ hdead_fin hv_dead_chain htx'_dead (by simpa using hj)
    hptrj_sub tl amount houtput_tl hrel ps self_def rk
    (by simp [tl]) (by simp [tl]) hnot_corrupt_self
  rcases hstrip_tx' with ⟨hptrj_sub', hstx'_eq⟩
  have hcoll : stx' = stx := by
    aapply hno_collision
    aapply List.IsSuffix.mem
  have hstrip_sub_eq_pub :
      tx'.strip bsub j (by simpa using hj) hptrj_sub' =
        tx_defend.strip bpub 0 hstx_h0 hstx_hptr := by grind
  have hinputs_eq : tx'.input_ptrs = tx_defend.input_ptrs := by
    exact congrArg Blockchain.StripedTransaction.inputs hstrip_sub_eq_pub
  have htx'_input_ptrs_single : tx'.input_ptrs = [ptr0] := by
    rw [hinputs_eq, hinput_ptrs_tx_defend]
  have hninputs_tx' : tx'.ninputs = 1 := by
    have hlen := congrArg List.length htx'_input_ptrs_single
    simpa [Blockchain.Transaction.input_ptrs, tx'.inputs.property] using hlen
  have hj_zero : j = 0 := by
    have : j < tx'.ninputs := by simpa [tx'.inputs.property] using hj
    omega
  have hprefix_sub_dead : bsub.transactions <+: bdead.transactions := by
    exact Blockchain.Transaction.get_sub_blockchain_transactions_prefix (b := bdead) (tx := tx')
  have hprefix_sub_fin : bsub.transactions <+: bfin.transactions :=
    hprefix_sub_dead.trans hprefix_dead_fin
  let h₁ : 0 < tx_defend.inputs.length := hstx_h0
  let h₂ : (tx_defend.inputs.val[0]'(by simpa using h₁)).outptr.valid bfin :=
    Blockchain.Pointer.valid_of_transactions_prefix hprefix_pub_fin hstx_hptr
  let h₃ : 0 < tx'.inputs.length := by
    simp [hninputs_tx']
  let h₄ : (tx'.inputs.val[0]'(by simpa using h₃)).outptr.valid bfin := by
    exact Blockchain.Pointer.valid_of_transactions_prefix hprefix_sub_fin
      (by simpa [hj_zero] using hptrj_sub')
  refine ⟨h₁, by simpa [bfin] using h₂, h₃, by simpa [bfin] using h₄, ?_⟩
  have hdef_grow :
      tx_defend.strip bpub 0 hstx_h0 hstx_hptr =
        tx_defend.strip bfin 0 hstx_h0 (Blockchain.Pointer.valid_of_transactions_prefix hprefix_pub_fin hstx_hptr) := by
    exact Blockchain.Transaction.strip.grows_transactions_prefix
      (b := bpub) (b' := bfin) (tx := tx_defend)
      hprefix_pub_fin 0 hstx_h0 hstx_hptr
  have htx'_grow :
      tx'.strip bsub j (by simpa using hj) hptrj_sub' =
        tx'.strip bfin j (by simpa using hj)
          (Blockchain.Pointer.valid_of_transactions_prefix hprefix_sub_fin hptrj_sub') := by
    exact Blockchain.Transaction.strip.grows_transactions_prefix
      (b := bsub) (b' := bfin) (tx := tx')
      hprefix_sub_fin j (by simpa using hj) hptrj_sub'
  calc
    tx_defend.strip bfin 0 h₁ h₂ = tx_defend.strip bpub 0 hstx_h0 hstx_hptr := by
      simpa [h₁, h₂] using hdef_grow.symm
    _ = tx'.strip bsub 0 h₃ (by simpa [hj_zero] using hptrj_sub') := by
      simpa [hj_zero, h₃] using hstrip_sub_eq_pub.symm
    _ = tx'.strip bfin 0 h₃ h₄ := by
      simpa [hj_zero, h₃, h₄] using htx'_grow
end Liveness
