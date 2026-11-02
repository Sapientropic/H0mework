import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Prefix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Transport
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

private def reindexGrant {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) : Mandate.Grant base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact grant

private theorem reindexGrant_event {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (reindexGrant sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent; cases sameWord; rfl

private theorem reindexGrant_index {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (reindexGrant sameCurrent sameWord grant).acceptance.item.val.index = grant.acceptance.item.val.index := by
  cases sameCurrent; cases sameWord; rfl

private theorem reindexGrant_items {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (reindexGrant sameCurrent sameWord grant).proposal.item.val = grant.proposal.item.val ∧
      (reindexGrant sameCurrent sameWord grant).acceptance.item.val = grant.acceptance.item.val := by
  cases sameCurrent; cases sameWord; exact ⟨rfl, rfl⟩

private theorem reindexGrant_actual {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) (actual : grant ∈ Mandate.grantsAt base scope first firstWord) :
    reindexGrant sameCurrent sameWord grant ∈ Mandate.grantsAt base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact actual

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)
  (rival : Opponent bound.source.code) (term : Cut.Term bound.source input cut)
  (active : bound.source.feedback? = some input)

abbrev OriginalGrant := Sigma fun birth : Fin (arrivalDepth bound cut + 1) =>
  Native.Authority.TracedGrant bound birth.val (arrivalDepth bound cut)
abbrev GrantAtArrival := {record : OriginalGrant bound cut // record ∈ Native.Authority.recordsAt bound (arrivalDepth bound cut)}

def migratedGrant (record : GrantAtArrival bound cut) :
    Mandate.Grant bound.base bound.scope
      (Native.Authority.currentAt (candidate bound input cut rival term) record.val.1.val)
      (Native.Authority.wordAt (candidate bound input cut rival term) record.val.1.val) :=
  reindexGrant (prefix_grant_current bound input cut rival term active _ (by omega))
    (prefix_grant_word bound input cut rival term active _ (by omega)) record.val.2.admission.grant

private theorem arrival_grant_is_actual (record : GrantAtArrival bound cut) :
    record.val.2.admission.grant ∈ Mandate.grantsAt bound.base bound.scope
      (Native.Authority.currentAt bound record.val.1.val) (Native.Authority.wordAt bound record.val.1.val) := by
  obtain ⟨birth, _, member⟩ := List.mem_flatMap.mp record.property
  obtain ⟨grant, actual, same⟩ := List.mem_map.mp member
  have : record.val = ⟨birth, Native.Authority.traceGrant bound birth.val (arrivalDepth bound cut) grant⟩ := same.symm
  cases record with
  | mk record proof => cases this; exact actual

theorem migrated_grant_is_in_the_candidates_actual_inventory (record : GrantAtArrival bound cut) :
    migratedGrant bound input cut rival term active record ∈ Mandate.grantsAt bound.base bound.scope
      (Native.Authority.currentAt (candidate bound input cut rival term) record.val.1.val)
      (Native.Authority.wordAt (candidate bound input cut rival term) record.val.1.val) :=
  reindexGrant_actual _ _ _ (arrival_grant_is_actual bound cut record)

theorem migrated_grant_keeps_both_original_signature_items (record : GrantAtArrival bound cut) :
    (migratedGrant bound input cut rival term active record).proposal.item.val = record.val.2.admission.grant.proposal.item.val ∧
      (migratedGrant bound input cut rival term active record).acceptance.item.val = record.val.2.admission.grant.acceptance.item.val :=
  reindexGrant_items _ _ _

theorem migrated_grant_keeps_the_original_acceptance_index (record : GrantAtArrival bound cut) :
    (migratedGrant bound input cut rival term active record).acceptance.item.val.index =
      record.val.2.admission.grant.acceptance.item.val.index :=
  reindexGrant_index _ _ _

theorem migrated_grant_keeps_the_original_election (record : GrantAtArrival bound cut) :
    (migratedGrant bound input cut rival term active record).electionEvent = record.val.2.admission.grant.electionEvent :=
  reindexGrant_event _ _ _

theorem migrated_grant_keeps_the_original_native_admission (record : GrantAtArrival bound cut) :
    (Mandate.admitGrant bound.base bound.scope _ _ (migratedGrant bound input cut rival term active record)).native.target =
      record.val.2.admission.native.target := by
  rw [record.val.2.admission.native_exact]
  change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler
    (migratedGrant bound input cut rival term active record).electionEvent).target = _
  rw [migrated_grant_keeps_the_original_election]
  rfl

theorem migrated_grant_keeps_the_entire_original_cut_state (record : GrantAtArrival bound cut) :
    (Mandate.Lifecycle.Observed.through (base := bound.base) (scope := bound.scope)
      (currentAt := Native.Authority.currentAt (candidate bound input cut rival term))
      (wordAt := Native.Authority.wordAt (candidate bound input cut rival term))
      (birth := record.val.1.val) (grant := migratedGrant bound input cut rival term active record)
      (arrivalDepth bound cut)).state = record.val.2.continuation.state := by
  rw [record.val.2.exact]
  apply Mandate.Lifecycle.Observed.through_state_congr (arrivalDepth bound cut)
    (reindexGrant_index _ _ _)
  · change (Mandate.admitGrant bound.base bound.scope _ _ (migratedGrant bound input cut rival term active record)).native.target = _
    rw [migrated_grant_keeps_the_original_native_admission, record.val.2.admission.native_exact]
    rfl
  · exact prefix_grant_current bound input cut rival term active
  · exact prefix_grant_word bound input cut rival term active

structure GrantContinuation where
  private mk ::
  original : GrantAtArrival bound cut
  after : Native.Authority.TracedGrant (candidate bound input cut rival term) original.val.1.val (terminalDepth bound input cut)
  after_exact : after = Native.Authority.traceGrant (candidate bound input cut rival term) original.val.1.val
    (terminalDepth bound input cut) (migratedGrant bound input cut rival term active original)

private def carryGrant (record : GrantAtArrival bound cut) : GrantContinuation bound input cut rival term active :=
  ⟨record, Native.Authority.traceGrant (candidate bound input cut rival term) record.val.1.val
    (terminalDepth bound input cut) (migratedGrant bound input cut rival term active record), rfl⟩

def grantContinuations : List (GrantContinuation bound input cut rival term active) :=
  (Native.Authority.recordsAt bound (arrivalDepth bound cut)).attach.map (carryGrant bound input cut rival term active)

def GrantContinuation.actualRun (record : GrantContinuation bound input cut rival term active) :
    (Mandate.Lifecycle.Observed.process (base := bound.base) (scope := bound.scope)
      (currentAt := Native.Authority.currentAt (candidate bound input cut rival term))
      (wordAt := Native.Authority.wordAt (candidate bound input cut rival term))
      (birth := record.original.val.1.val) (grant := migratedGrant bound input cut rival term active record.original)).Run
      record.original.val.2.continuation.state record.after.continuation.state := by
  rw [record.after_exact]
  dsimp only [Native.Authority.traceGrant]
  rw [← migrated_grant_keeps_the_entire_original_cut_state bound input cut rival term active record.original]
  have ending : terminalDepth bound input cut = arrivalDepth bound cut + Cut.horizon bound.source input cut := by
    dsimp only [terminalDepth, arrivalDepth, Cut.finish, Cut.start]
    omega
  rw [ending]
  exact Mandate.Lifecycle.Observed.fromActualCut (arrivalDepth bound cut) (Cut.horizon bound.source input cut)

theorem GrantContinuation.after_is_in_the_candidates_actual_census
    (record : GrantContinuation bound input cut rival term active) :
    (⟨⟨record.original.val.1.val, by
      have born := record.original.val.1.isLt
      dsimp only [arrivalDepth, terminalDepth, Cut.finish, Cut.start] at *
      omega⟩, record.after⟩ : Sigma fun birth : Fin (terminalDepth bound input cut + 1) =>
        Native.Authority.TracedGrant (candidate bound input cut rival term) birth.val (terminalDepth bound input cut)) ∈
      (Native.Authority.generate (candidate bound input cut rival term) (terminalDepth bound input cut)).mandates := by
  rw [record.after_exact]
  exact Native.Authority.every_actual_grant_is_admitted _ _ _ _
    (migrated_grant_is_in_the_candidates_actual_inventory bound input cut rival term active record.original)

theorem grant_migration_keeps_the_entire_original_census :
    (grantContinuations bound input cut rival term active).map (fun record => record.original.val) =
      Native.Authority.recordsAt bound (arrivalDepth bound cut) := by
  simp [grantContinuations, List.map_map, Function.comp_def, carryGrant]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority
