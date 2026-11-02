import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Native.Challenge

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Authority.Trace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (raw : List (Option model.source.code.Policy))
  (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions) (budget : ℚ)
  (rival : Opponent model.source.code)
  (paid : Source.Paid model.source input cut raw (Cut.horizon model.source input cut) party good budget rival)
  (active : model.source.feedback? = some input) (empty : model.source.continuation = [])

include paid active empty in
theorem original_grant_lifecycle (record : RawAuthority.GrantAtArrival model cut) :
    grantImage (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget))
      record.val.1.val (RawAuthority.terminalDepth model input cut)
      (Native.Authority.traceGrant _ _ _ (RawAuthority.migratedGrant model input cut rival
        (representative model input cut raw party good floor budget) active record)) =
    grantImage (RawAuthority.candidate model input cut rival raw) record.val.1.val (RawAuthority.terminalDepth model input cut)
      (Native.Authority.traceGrant _ _ _ (RawAuthority.migratedGrant model input cut rival raw active record)) := by
  have newItems := RawAuthority.migrated_grant_keeps_both_original_signature_items model input cut rival
    (representative model input cut raw party good floor budget) active record
  have oldItems := RawAuthority.migrated_grant_keeps_both_original_signature_items model input cut rival raw active record
  have items := And.intro (newItems.1.trans oldItems.1.symm) (newItems.2.trans oldItems.2.symm)
  have election := (RawAuthority.migrated_grant_keeps_the_original_election model input cut rival
    (representative model input cut raw party good floor budget) active record).trans
      (RawAuthority.migrated_grant_keeps_the_original_election model input cut rival raw active record).symm
  have initial : Mandate.Lifecycle.Observed.initialState model.base model.scope
      (Native.Authority.currentAt (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)))
      (Native.Authority.wordAt (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)))
      record.val.1.val (RawAuthority.migratedGrant model input cut rival (representative model input cut raw party good floor budget) active record) =
    Mandate.Lifecycle.Observed.initialState model.base model.scope
      (Native.Authority.currentAt (RawAuthority.candidate model input cut rival raw))
      (Native.Authority.wordAt (RawAuthority.candidate model input cut rival raw)) record.val.1.val
      (RawAuthority.migratedGrant model input cut rival raw active record) := by
    change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler _).target = _
    rw [election]
    rfl
  have index := congrArg ExecutionItem.index items.2
  have state := Mandate.Lifecycle.Observed.through_state_congr (RawAuthority.terminalDepth model input cut) index initial
    (current model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
    (word model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
  have final := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have history := grant_through_images_congr model.source.code (RawAuthority.terminalDepth model input cut) index initial
    (current model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
    (word model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
  have original := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl,congrArg (itemImage model.source.code) items.1,congrArg (itemImage model.source.code) items.2,
    congrArg grantObligationImage original,congrArg grantObligationImage final,history⟩

include paid active empty in
theorem original_grant_manifest :
    (RawAuthority.manifest model input cut rival (representative model input cut raw party good floor budget) active).originalGrants =
      (RawAuthority.manifest model input cut rival raw active).originalGrants := by
  simp only [RawAuthority.manifest,RawAuthority.grantContinuations,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro record _
  exact congrArg (fun image => (grantImage model record.val.1.val _ record.val.2,image))
    (original_grant_lifecycle model input cut raw party good floor budget rival paid active empty record)

include paid active empty in
theorem every_world_and_actual_instruction_is_preserved :
    (RawAuthority.manifest model input cut rival (representative model input cut raw party good floor budget) active).worlds =
      (RawAuthority.manifest model input cut rival raw active).worlds := by
  apply List.map_congr_left
  intro ordinal member
  exact Native.Coupling.History.occurrence_image model.source.code
    (RawAuthority.candidate model input cut rival raw).source.input
    (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)).source.input
    rfl rfl (Cut.finish model.source input cut)
    (events model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
    ordinal (List.mem_range.mp member)

include paid active empty in
/-- Every original and newborn responsibility is read from its own actual native history. -/
theorem the_complete_raw_native_manifest_is_preserved :
    RawAuthority.manifest model input cut rival (representative model input cut raw party good floor budget) active =
      RawAuthority.manifest model input cut rival raw active := by
  apply (Manifest.mk.injEq ..).mpr
  exact ⟨every_world_and_actual_instruction_is_preserved model input cut raw party good floor budget rival paid active empty,
    original_grant_manifest model input cut raw party good floor budget rival paid active empty,
    original_challenge_manifest model input cut raw party good floor budget rival paid active empty,
    complete_grant_census model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty,
    complete_candidate_challenge_manifest model input cut raw party good floor budget rival paid active empty⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport
