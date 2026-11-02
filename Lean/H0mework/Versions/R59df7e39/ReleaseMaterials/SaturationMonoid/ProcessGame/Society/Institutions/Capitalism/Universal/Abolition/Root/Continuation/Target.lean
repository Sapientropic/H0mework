import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Living
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Original

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)
  (request : Request Party Good Port Technology Instrument)

def targetInitial := (livingRoot input frame request).toAuthoritativeRoot.toRoot.initialVisit

def sourceEntry := Financial.Installation.Runtime.entry input frame.native frame.visit.current

def occurrencePresentation (unique : OriginalOccurrenceUnique input frame) : ConstructivePresentation
    (frame.native.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt frame.visit.current)
    ((livingRoot input frame request).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (targetInitial input frame request).current) where
  forward := fun _ => emitted input frame request (initial input frame)
  backward := fun _ => frame.native.root.emitted frame.visit.current
  backward_forward := fun occurrence => (unique frame.visit.current occurrence).symm
  forward_backward := fun occurrence => (occurrence_eq_emitted input frame request occurrence).symm

def initialRow :
    ((livingRoot input frame request).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input frame request))).GeneratedEntryRowAt (sourceEntry input frame) :=
  (((livingRoot input frame request).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite (targetInitial input frame request))).canonicalGeneratedEntryRow?
      (sourceEntry input frame)).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((livingRoot input frame request).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input frame request))).occurrence
    ((livingRoot input frame request).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input frame request))).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((livingRoot input frame request).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input frame request))).wholeLedgerWriteBack).get (by rfl)

theorem first_write_executes_the_original_opcode :
    (firstSuccessor input frame request).targetCurrent = input.law.step (initial input frame) request := rfl

private def targetFromOriginal (unique : OriginalOccurrenceUnique input frame)
    (fee : Review.FeeScope request)
    (paid : Review.PaymentAt input.law request (initial input frame))
    (event : ExactTemporalCausalRootEventAt frame.native.root.toAuthoritativeRoot.toLedgerRoot
      (frame.temporal input)) :
    SourceNativeSequentialActualActionTargetAt frame.native.root (frame.temporal input)
      event (sourceEntry input frame) frame.authority := by
  rw [event.eq_generated]
  exact {
    TargetN := N input frame
    translation := translation frame.native.N _ (initial input frame)
    TargetV := V input frame request
    targetRoot := livingRoot input frame request
    targetTheory := TheoryState.rootSemantic (N input frame)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation input frame request unique
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (translation frame.native.N _ (initial input frame)).oldOpenLedger (oldSupport input frame)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry, ⟨rfl⟩⟩⟩
    translatedSourceEntryRow := initialRow input frame request
    firstSuccessor := firstSuccessor input frame request
    canonical_targetNextVisit_eq := by
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl
    Answer := ExecutionAt input frame request (initial input frame)
    answer := execution input frame request (initial input frame)
    Receipt := fun answer => ULift.{3, 0} (PLift
      ((firstSuccessor input frame request).targetCurrent = answer.after ∧
        answer.after.stock fee.payer fee.good + fee.amount = answer.before.stock fee.payer fee.good ∧
        answer.after.claims = answer.before.claims ∧
        answer.after.clock = answer.before.clock ∧ answer.after.round = answer.before.round))
    receipt := ⟨⟨rfl, fee_first_write_is_material input frame request fee paid⟩⟩ }

def feeTarget (depth count : Nat)
    (fee : Review.FeeScope request)
    (paid : Review.PaymentAt input.law request
      (initial input (Financial.Installation.Runtime.frames input depth count)))
    (event : ExactTemporalCausalRootEventAt
      (Financial.Installation.Runtime.frames input depth count).native.root.toAuthoritativeRoot.toLedgerRoot
      ((Financial.Installation.Runtime.frames input depth count).temporal input)) :=
  targetFromOriginal input (Financial.Installation.Runtime.frames input depth count) request
    (actual_frame_occurrence_unique input depth count) fee paid event

def feeProgram (depth count : Nat)
    (fee : Review.FeeScope request)
    (paid : Review.PaymentAt input.law request
      (initial input (Financial.Installation.Runtime.frames input depth count))) :
    SourceNativeSequentialActualActionProgramAt
      (Financial.Installation.Runtime.frames input depth count).native.root
      ((Financial.Installation.Runtime.frames input depth count).temporal input)
      (sourceEntry input (Financial.Installation.Runtime.frames input depth count))
      (Financial.Installation.Runtime.frames input depth count).authority where
  targetAt := feeTarget input request depth count fee paid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
