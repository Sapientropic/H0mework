import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
  (term : Cut.Term bound.source input cut)
  (active : bound.source.feedback? = some input) (empty : bound.source.continuation = [])

include active empty in
theorem joint_world_images :
    worlds bound input cut (Future.jointOpponent bound.source input cut rival) term = worlds bound input cut rival term := by
  unfold worlds
  apply List.map_congr_left
  intro ordinal member
  have inside := List.mem_range.mp member
  have actual := Future.joint_occurrences bound.source input cut rival term.val active empty term.property ordinal inside
  change Identity.OccurrenceImage.mk
    (Identity.visitImage bound.source.code (ProgrammeHistory.visitAt _ ordinal).current) _ = _
  exact congrArg₂ Identity.OccurrenceImage.mk (congrArg (Identity.visitImage bound.source.code) actual.1) actual.2

include active empty in
private theorem joint_grant_current (visit : Nat) (inside : visit ≤ terminalDepth bound input cut) :
    Native.Authority.currentAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) visit =
      Native.Authority.currentAt (candidate bound input cut rival term) visit :=
  Future.joint_current bound.source input cut rival term.val active empty term.property (visit + 1)
    (by dsimp only [terminalDepth, Cut.finish, Cut.start, Cut.horizon] at *; omega)

include active empty in
private theorem joint_grant_word (visit : Nat) (inside : visit ≤ terminalDepth bound input cut) :
    Native.Authority.wordAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) visit =
      Native.Authority.wordAt (candidate bound input cut rival term) visit :=
  (Future.joint_occurrences bound.source input cut rival term.val active empty term.property (visit + 1)
    (by dsimp only [terminalDepth, Cut.finish, Cut.start, Cut.horizon] at *; omega)).2

def JointGrantAgreement (record : GrantAtArrival bound cut) : Prop :=
    let original := Mandate.Lifecycle.Observed.through (base := bound.base) (scope := bound.scope)
      (currentAt := Native.Authority.currentAt (candidate bound input cut rival term))
      (wordAt := Native.Authority.wordAt (candidate bound input cut rival term))
      (birth := record.val.1.val) (grant := migratedGrant bound input cut rival term active record) (terminalDepth bound input cut)
    let finite := Mandate.Lifecycle.Observed.through (base := bound.base) (scope := bound.scope)
      (currentAt := Native.Authority.currentAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      (wordAt := Native.Authority.wordAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      (birth := record.val.1.val) (grant := migratedGrant bound input cut (Future.jointOpponent bound.source input cut rival) term active record)
      (terminalDepth bound input cut)
    finite.state = original.state ∧ grantHistoryImage bound.source.code finite = grantHistoryImage bound.source.code original

include active empty in
theorem joint_original_grant_state_and_receipts (record : GrantAtArrival bound cut) :
    JointGrantAgreement bound input cut rival term active record := by
  have index := (migrated_grant_keeps_the_original_acceptance_index bound input cut
    (Future.jointOpponent bound.source input cut rival) term active record).trans
      (migrated_grant_keeps_the_original_acceptance_index bound input cut rival term active record).symm
  have initial : Mandate.Lifecycle.Observed.initialState bound.base bound.scope
      (Native.Authority.currentAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      (Native.Authority.wordAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      record.val.1.val (migratedGrant bound input cut (Future.jointOpponent bound.source input cut rival) term active record) =
        Mandate.Lifecycle.Observed.initialState bound.base bound.scope
          (Native.Authority.currentAt (candidate bound input cut rival term))
          (Native.Authority.wordAt (candidate bound input cut rival term)) record.val.1.val
          (migratedGrant bound input cut rival term active record) :=
    (migrated_grant_keeps_the_original_native_admission bound input cut
      (Future.jointOpponent bound.source input cut rival) term active record).trans
        (migrated_grant_keeps_the_original_native_admission bound input cut rival term active record).symm
  exact ⟨Mandate.Lifecycle.Observed.through_state_congr _ index initial
      (joint_grant_current bound input cut rival term active empty) (joint_grant_word bound input cut rival term active empty),
    grant_through_images_congr bound.source.code _ index initial
      (joint_grant_current bound input cut rival term active empty) (joint_grant_word bound input cut rival term active empty)⟩

include active empty in
theorem joint_original_grant_image (record : GrantAtArrival bound cut) :
    continuedGrantImage bound input cut (Future.jointOpponent bound.source input cut rival) term active record =
      continuedGrantImage bound input cut rival term active record := by
  have agreement := joint_original_grant_state_and_receipts bound input cut rival term active empty record
  have state := agreement.1
  have receipts := agreement.2
  have obligation := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have finiteItems := migrated_grant_keeps_both_original_signature_items bound input cut
    (Future.jointOpponent bound.source input cut rival) term active record
  have actualItems := migrated_grant_keeps_both_original_signature_items bound input cut rival term active record
  have election := (migrated_grant_keeps_the_original_election bound input cut
    (Future.jointOpponent bound.source input cut rival) term active record).trans
      (migrated_grant_keeps_the_original_election bound input cut rival term active record).symm
  have initial := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl, congrArg (itemImage bound.source.code) (finiteItems.1.trans actualItems.1.symm),
    congrArg (itemImage bound.source.code) (finiteItems.2.trans actualItems.2.symm),
    congrArg grantObligationImage initial, congrArg grantObligationImage obligation, receipts⟩

include active empty in
theorem joint_original_grant_manifest :
    (generate bound input cut (Future.jointOpponent bound.source input cut rival) term active).originalGrants =
      (generate bound input cut rival term active).originalGrants := by
  simp only [generate, grantContinuations, List.map_map]
  change (Native.Authority.recordsAt bound (arrivalDepth bound cut)).attach.map
      (fun record => (grantImage bound record.val.1.val _ record.val.2,
        continuedGrantImage bound input cut (Future.jointOpponent bound.source input cut rival) term active record)) =
    (Native.Authority.recordsAt bound (arrivalDepth bound cut)).attach.map
      (fun record => (grantImage bound record.val.1.val _ record.val.2, continuedGrantImage bound input cut rival term active record))
  apply List.map_congr_left
  intro record _
  exact congrArg (Prod.mk _) (joint_original_grant_image bound input cut rival term active empty record)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
