import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

abbrev frame := Financial.Installation.Runtime.frames input depth count

variable (datum : Datum input (frame input depth count))

def originalOccurrence := (frame input depth count).native.root.emitted (frame input depth count).visit.current
def code := datum.reader (originalOccurrence input depth count)
def result := attemptAt input (frame input depth count) datum (originalOccurrence input depth count)

def firstSuccessor := Continuation.firstSuccessor input (frame input depth count)
  (code input depth count datum).request

def ResultReceipt (answer : ResultAt input (frame input depth count) datum (originalOccurrence input depth count)) : Prop :=
  answer = result input depth count datum ∧
    match answer with
    | .inl _ =>
      let fee := (code input depth count datum).scope
      let before := Continuation.initial input (frame input depth count)
      let after := (firstSuccessor input depth count datum).targetCurrent
      after.stock fee.payer fee.good + fee.amount = before.stock fee.payer fee.good ∧
        after.claims = before.claims ∧ after.clock = before.clock ∧ after.round = before.round
    | .inr _ => (firstSuccessor input depth count datum).targetCurrent =
        Continuation.initial input (frame input depth count)

theorem result_receipt : ResultReceipt input depth count datum (result input depth count datum) := by
  refine ⟨rfl, ?_⟩
  cases observed : result input depth count datum with
  | inl paid =>
      exact Continuation.fee_first_write_is_material input (frame input depth count)
        (code input depth count datum).request (code input depth count datum).scope paid
  | inr blocked => exact blocked.actual_source_preserves_current

def targetAt (event : ExactTemporalCausalRootEventAt
    (root input (frame input depth count) datum).toAuthoritativeRoot.toLedgerRoot
    (visit input (frame input depth count) datum)) :
    SourceNativeSequentialActualActionTargetAt (root input (frame input depth count) datum)
      (visit input (frame input depth count) datum) event
      (Continuation.sourceEntry input (frame input depth count))
      (authority input (frame input depth count) datum) := by
  rw [event.eq_generated]
  let request := (code input depth count datum).request
  exact {
    TargetN := Continuation.N input (frame input depth count)
    translation := Continuation.translation (frame input depth count).native.N _
      (Continuation.initial input (frame input depth count))
    TargetV := Continuation.V input (frame input depth count) request
    targetRoot := Continuation.livingRoot input (frame input depth count) request
    targetTheory := TheoryState.rootSemantic (Continuation.N input (frame input depth count))
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := Continuation.occurrencePresentation input (frame input depth count) request
      (Continuation.actual_frame_occurrence_unique input depth count)
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (Continuation.translation (frame input depth count).native.N _
      (Continuation.initial input (frame input depth count))).oldOpenLedger
      (Continuation.oldSupport input (frame input depth count))
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry, ⟨rfl⟩⟩⟩
    translatedSourceEntryRow := Continuation.initialRow input (frame input depth count) request
    firstSuccessor := firstSuccessor input depth count datum
    canonical_targetNextVisit_eq := by
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl
    Answer := ResultAt input (frame input depth count) datum (originalOccurrence input depth count)
    answer := result input depth count datum
    Receipt := fun answer => ULift.{3, 0} (PLift (ResultReceipt input depth count datum answer))
    receipt := ⟨⟨result_receipt input depth count datum⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt
    (root input (frame input depth count) datum) (visit input (frame input depth count) datum)
    (Continuation.sourceEntry input (frame input depth count))
    (authority input (frame input depth count) datum) where
  targetAt := targetAt input depth count datum

def sourceEvent := (root input (frame input depth count) datum).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (visit input (frame input depth count) datum)

def generated := (program input depth count datum).generate (sourceEvent input depth count datum)

theorem actual_target_is_the_original_microstep :
    (generated input depth count datum).target.firstSuccessor.targetCurrent =
      input.law.step (Continuation.initial input (frame input depth count)) (code input depth count datum).request := rfl

theorem source_rejection_keeps_the_original_physical_current
    (blocked : Review.Blockage input.law (code input depth count datum).request
      (code input depth count datum).scope (Continuation.initial input (frame input depth count))) :
    (generated input depth count datum).target.firstSuccessor.targetCurrent =
      Continuation.initial input (frame input depth count) := blocked.actual_source_preserves_current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
