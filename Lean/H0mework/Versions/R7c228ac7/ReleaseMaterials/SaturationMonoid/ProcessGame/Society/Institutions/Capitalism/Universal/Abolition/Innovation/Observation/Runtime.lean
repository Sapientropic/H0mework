import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Adaptive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Macro.Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (originalReader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input))


private def OriginReaderAt
    (current : Macro.Runtime.ActivatedFrame (review := review) input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Macro.Ingress.cut input depth sourceStart)) : Prop :=
  match current with
  | .original frame => frame.package.reader = originalReader
  | .enacted origin _ _ => origin.reader = originalReader

private theorem originReader_next
    (current : Macro.Runtime.ActivatedFrame (review := review) input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Macro.Ingress.cut input depth sourceStart))
    (sourced : OriginReaderAt input depth sourceStart prefixLimit renewalLimit originalReader review current) :
    OriginReaderAt input depth sourceStart prefixLimit renewalLimit originalReader review current.next := by
  cases current with
  | enacted origin admission frame => exact sourced
  | original frame =>
      dsimp only [Macro.Runtime.ActivatedFrame.next]
      cases selected : frame.query with
      | internal work =>
          change frame.internalNext.package.reader = originalReader
          have preserved : frame.internalNext.package.reader = frame.package.reader := by
            unfold Macro.Runtime.Frame.internalNext
            split <;> rfl
          exact preserved.trans sourced
      | raw germ =>
          dsimp only
          cases chosen : Functions.Revision.InitialAdmission.select (Macro.Runtime.Frame.controlOrigin frame germ) with
          | admitted admission => exact sourced
          | obstructed failed => exact sourced

theorem every_actual_origin_keeps_the_original_installed_reader (tick : Nat) :
    OriginReaderAt input depth sourceStart prefixLimit renewalLimit originalReader review
      (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick) := by
  induction tick with
  | zero => rfl
  | succ tick prior => exact originReader_next input depth sourceStart prefixLimit renewalLimit originalReader review _ prior

variable {input depth sourceStart datum prefixLimit renewalLimit originalReader review}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Macro.Ingress.cut input depth sourceStart)}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum
    prefixLimit renewalLimit originalReader tick = .enacted origin admission frame)

include selected

theorem the_actual_origin_reader_is_not_caller_supplied : origin.reader = originalReader := by
  have sourced := every_actual_origin_keeps_the_original_installed_reader input depth sourceStart datum
    prefixLimit renewalLimit originalReader review tick
  rw [selected] at sourced
  exact sourced

theorem the_observation_cut_is_the_literal_mixed_epoch_source :
    (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick).actualState =
        Physical.Public.stateAt input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot.past ∧
      (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick).interpreter =
        Physical.Public.interpreter input ∧
      (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick).nativeAccount =
        frame.account := by
  rw [selected]
  exact ⟨rfl, rfl, rfl⟩

variable (rule : Rule Party Good Port Technology Instrument) (programme : Programme rule)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))

/- This equality concerns only the original consumed source cut. It is
not a paid observation, result, new account, or successful continuation. -/
variable (sourcePrefix : oldPast = origin.germ.snapshot.past)

include sourcePrefix

theorem the_actual_observation_reader_emits_its_source_generated_proposal
    (installed : originalReader = reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) :
    Macro.Runtime.originalProposal frame = scheduledProposal input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme frame.snapshot.past := by
  have sourced := the_actual_origin_reader_is_not_caller_supplied frame tick selected
  unfold Macro.Runtime.originalProposal
  have sameRead := congrFun (congrFun (sourced.trans installed) frame.actual.readerCursor) frame.account
  trans reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme
    frame.actual.readerCursor frame.account
  · exact sameRead
  change reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme
      (Physical.receive (Physical.Prefix.cursor (origin.germ.snapshot.past ++ frame.snapshot.past)) frame.snapshot.incoming)
      frame.account = _
  simp only [reader, Physical.receive, Physical.Prefix.past_readback]
  rw [← sourcePrefix, List.drop_left]

theorem a_source_generated_code_is_consumed_by_the_original_actual_next
    (installed : originalReader = reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
    (complete : ¬ frame.HasWork)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : programme (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule frame.snapshot.past) = some word) :
    frame.actual.proposal frame.reader = .code ⟨word⟩ ∧
      frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.code ⟨word⟩)) ∧
      frame.next.account = frame.account ∧
      Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader (tick + 1) =
        .enacted origin admission frame.next := by
  have raw := the_actual_observation_reader_emits_its_source_generated_proposal frame tick selected rule programme oldPast sourcePrefix installed
  simp only [scheduledProposal, generated] at raw
  have selectedRaw := Macro.Runtime.every_actual_public_proposal_is_the_current_source_selection datum originalReader frame tick selected
  rw [raw] at selectedRaw
  change frame.actual.proposal frame.reader = .code ⟨word⟩ at selectedRaw
  refine ⟨selectedRaw, ?_, ?_, ?_⟩
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Macro.Public.Scope.selectedCursor input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [selectedRaw]
    rfl
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete
  · change (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick).next = _
    rw [selected]
    rfl

theorem consuming_a_pure_code_does_not_rewrite_the_physical_past
    (installed : originalReader = reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
    (complete : ¬ frame.HasWork)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : programme (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule frame.snapshot.past) = some word) :
    Physical.Public.stateAt input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.next.snapshot.past =
      Physical.Public.stateAt input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot.past := by
  have consumed := a_source_generated_code_is_consumed_by_the_original_actual_next frame tick selected rule programme oldPast
    sourcePrefix installed complete word generated
  rw [consumed.2.1]
  exact Physical.Public.consumed_input_generates_its_own_after input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
    origin.germ.snapshot.past (Physical.receive frame.snapshot (.code ⟨word⟩))

theorem the_same_engine_consumes_the_generated_code_and_preserves_the_whole_root_law
    (installed : originalReader = reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
    (complete : ¬ frame.HasWork)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : programme (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule frame.snapshot.past) = some word) :
    (Macro.Runtime.event (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader
      (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader (tick + 1))).next.engine.node =
        .active frame.next.presentation ∧
      type_of% (Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review)
        input depth sourceStart datum prefixLimit renewalLimit originalReader
        (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader (tick + 1))) := by
  have consumed := a_source_generated_code_is_consumed_by_the_original_actual_next frame tick selected rule programme oldPast
    sourcePrefix installed complete word generated
  constructor
  · have next := Macro.Runtime.actual_next (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick _
      (Macro.Runtime.run_is_the_original_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader tick)
      (Macro.Runtime.event (review := review) input depth sourceStart datum prefixLimit renewalLimit originalReader _)
    rw [consumed.2.2.2] at next
    exact next
  · exact Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review)
      input depth sourceStart datum prefixLimit renewalLimit originalReader _

#print axioms the_actual_origin_reader_is_not_caller_supplied
#print axioms the_observation_cut_is_the_literal_mixed_epoch_source
#print axioms a_source_generated_code_is_consumed_by_the_original_actual_next
#print axioms the_same_engine_consumes_the_generated_code_and_preserves_the_whole_root_law

omit selected sourcePrefix in
theorem the_registered_observation_programme_generates_its_same_actual_root_next
    (actual : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit
      (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) tick =
        .enacted origin admission frame)
    (sourceCut : oldPast = origin.germ.snapshot.past)
    (complete : ¬ frame.HasWork) :
    (∀ word, programme (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule
        frame.snapshot.past) = some word →
      frame.actual.proposal frame.reader = .code ⟨word⟩ ∧
        frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.code ⟨word⟩)) ∧
        frame.next.account = frame.account) ∧
      (programme (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule
        frame.snapshot.past) = none → Macro.Runtime.originalProposal frame =
        (if hasOwnAttempt rule frame.snapshot.past then .advance else .primitive rule.request)) ∧
      (Macro.Runtime.event (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
        (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit
          (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
          (tick + 1))).next.engine.node = .active frame.next.presentation ∧
      frame.account.current.history <+: frame.next.account.current.history ∧
      frame.account.current.slots.map (Epoch.Finance.slotClaim input depth (Macro.Ingress.cut input depth sourceStart)) <+:
        frame.next.account.current.slots.map (Epoch.Finance.slotClaim input depth (Macro.Ingress.cut input depth sourceStart)) ∧
      type_of% (Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review)
        input depth sourceStart datum prefixLimit renewalLimit
        (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
        (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit
          (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) (tick + 1))) := by
  refine ⟨?_, ?_, ?_, frame.next_keeps_the_complete_original_history, frame.next_keeps_all_original_claims, ?_⟩
  · intro word generated
    have consumed := a_source_generated_code_is_consumed_by_the_original_actual_next frame tick actual rule programme oldPast
      sourceCut rfl complete word generated
    exact ⟨consumed.1, consumed.2.1, consumed.2.2.1⟩
  · intro generated
    have raw := the_actual_observation_reader_emits_its_source_generated_proposal frame tick actual rule programme oldPast sourceCut rfl
    simpa only [scheduledProposal, generated] using raw
  · have next := Macro.Runtime.actual_next (review := review) input depth sourceStart datum prefixLimit renewalLimit
      (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) tick _
      (Macro.Runtime.run_is_the_original_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) tick)
      (Macro.Runtime.event (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) _)
    change (Macro.Runtime.event (review := review) input depth sourceStart datum prefixLimit renewalLimit
        (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
        (Macro.Runtime.run (review := review) input depth sourceStart datum prefixLimit renewalLimit
          (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) (tick + 1))).next.engine.node =
        .active (Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit
          (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) tick).next.presentation at next
    rw [actual] at next
    exact next
  · exact Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review) input depth sourceStart datum prefixLimit renewalLimit
      (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme) _

#print axioms the_registered_observation_programme_generates_its_same_actual_root_next

omit selected sourcePrefix in
theorem the_sensor_code_is_a_real_next_candidate_and_then_yields_advance
    (choose : Fin rule.code.signals → RawEvent Party Good Port Technology Instrument)
    (actual : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit
      (reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule
        (programmeFromSensor rule choose)) tick = .enacted origin admission frame)
    (sourceCut : oldPast = origin.germ.snapshot.past)
    (complete : ¬ frame.HasWork) (word : RawEvent Party Good Port Technology Instrument)
    (generated : programmeFromSensor rule choose
      (localHistory input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule frame.snapshot.past) = some word) :
    word ∈ Functions.Revision.Adaptive.candidates input depth (Macro.Ingress.cut input depth sourceStart)
        prefixLimit renewalLimit origin.germ.snapshot.past frame.next.snapshot ∧
      Macro.Runtime.originalProposal frame.next = .advance := by
  have consumed := a_source_generated_code_is_consumed_by_the_original_actual_next frame tick actual rule
    (programmeFromSensor rule choose) oldPast sourceCut rfl complete word generated
  constructor
  · have listed : word ∈ Functions.Revision.Adaptive.consumedProposals frame.next.snapshot := by
      unfold Functions.Revision.Adaptive.consumedProposals
      rw [consumed.2.1]
      apply List.mem_flatMap.mpr
      refine ⟨.code ⟨word⟩, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact List.mem_singleton_self _
    simp only [Functions.Revision.Adaptive.candidates, List.mem_append, listed, true_or, or_true]
  · have raw := the_actual_observation_reader_emits_its_source_generated_proposal frame.next (tick + 1)
      consumed.2.2.2 rule (programmeFromSensor rule choose) oldPast sourceCut rfl
    rw [scheduledProposal, consumed.2.1] at raw
    simp only [Physical.next, Physical.receive] at raw
    rw [its_own_code_is_retained_only_as_its_original_attempt,
      its_own_code_attempt_generates_the_next_advance] at raw
    simpa only [hasOwnAttempt, List.any_append, List.any_cons, List.any_nil, Bool.or_true,
      Bool.true_or, ↓reduceIte] using raw

#print axioms the_sensor_code_is_a_real_next_candidate_and_then_yields_advance

omit selected sourcePrefix in
private theorem internal_snapshot (work : frame.HasWork) : frame.next.snapshot = frame.snapshot := by
  rw [Macro.Public.Runtime.Frame.next, dif_pos work]
  unfold Macro.Public.Runtime.Frame.internalNext
  split
  · exact frame.born_snapshot _
  · exact frame.ordinary_snapshot work _

omit selected sourcePrefix in
theorem the_generated_internal_drain_keeps_the_same_actual_snapshot : frame.drained.snapshot = frame.snapshot := by
  suffices ∀ mass (current : Macro.Public.Runtime.Frame origin admission), current.sourceMass = mass →
      current.drained.snapshot = current.snapshot from this _ frame rfl
  intro mass
  induction mass using Nat.strong_induction_on with
  | h mass smaller =>
      intro current same
      by_cases work : current.HasWork
      · have lowered : current.next.sourceMass < mass := by
          rw [← same]
          exact current.every_internal_next_strictly_lowers_the_actual_source work
        have tail := smaller current.next.sourceMass lowered current.next rfl
        rw [Macro.Public.Runtime.Frame.drained, Macro.Public.Runtime.Frame.drain, dif_pos work]
        change (current.visits (current.next.drain.val + 1)).snapshot = _
        rw [Macro.Public.Runtime.Frame.visits, Function.iterate_succ_apply]
        exact tail.trans (internal_snapshot current work)
      · rw [Macro.Public.Runtime.Frame.drained, Macro.Public.Runtime.Frame.drain, dif_neg work]
        rfl

theorem the_actual_reader_consumes_its_own_initial_fee
    (installed : originalReader = reader input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit oldPast rule programme)
    (complete : ¬ frame.HasWork)
    (generated : scheduledProposal input depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      oldPast rule programme frame.snapshot.past = .primitive rule.request) :
    frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.primitive rule.request)) ∧
      frame.next.account = frame.account := by
  have raw := the_actual_observation_reader_emits_its_source_generated_proposal frame tick selected rule programme oldPast sourcePrefix installed
  rw [generated] at raw
  have parsed := Macro.Runtime.every_actual_public_proposal_is_the_current_source_selection datum originalReader frame tick selected
  rw [raw] at parsed
  change frame.actual.proposal frame.reader = .primitive rule.request at parsed
  constructor
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Macro.Public.Scope.selectedCursor input depth (Macro.Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [parsed]
    rfl
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete

#print axioms the_generated_internal_drain_keeps_the_same_actual_snapshot
#print axioms the_actual_reader_consumes_its_own_initial_fee

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation
