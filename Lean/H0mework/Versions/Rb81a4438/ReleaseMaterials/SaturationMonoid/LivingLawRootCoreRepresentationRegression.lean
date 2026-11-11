import H0mework.Foundation.Authority.Factorization
import H0mework.Arithmetic.PrimeShadow.LivingLawRootSourceNativeAuthorityRegression
import H0mework.Arithmetic.PrimeShadow.LivingLawRootAnswerNextHistoryRegression

/-!
# Canonical root-core representation regression

The fixture has a complete source-native ledger compiler and source-fixed
projection law.  These checks ensure that the exact temporal occurrence owns
the ledger evolution while installed coordinates remain direct restrictions
of that law.  A current-indexed compatibility root value cannot be promoted
into this private source-native realization.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace RootCoreRepresentationRegression

open ConstructiveRoot
open SourceNativeRootAuthorityRegression
open ConstructiveRoot.RootAnswerNextHistoryRegression

def realized : SourceNativeTemporalVisitGeneratedEvolutionAt
    questionWorld.toLedgerRoot (.finite questionVisit) :=
  questionWorld.toLedgerRoot.generatedAtTemporalVisit (.finite questionVisit)

def causalVisit : SourceNativeTemporalVisitAt questionWorld.toLedgerRoot :=
  .finite questionVisit

def causalProcess : CausalCore.Process questionWorld.toCausalWorld :=
  questionWorld.canonicalCausalProcess

/-- The canonical causal presentation computes the same whole-ledger output
as the fixed root compiler. -/
theorem causal_process_generates_root_ledger :
    HEq (causalProcess.generate
      (show questionWorld.toCausalWorld.Current from
        (.finite questionVisit))).toLedgerReadout.wholeLedgerWriteBack
      (questionWorld.toLedgerRoot.generatedLedgerAt questionVisit.current) :=
  questionWorld.process_generate_wholeLedger_eq_canonical
    causalProcess
    (.finite questionVisit)

/-- Every process returning the same root causal carrier has the canonical
whole-ledger readout at this exact visit. -/
theorem any_process_generates_root_ledger
    (process : CausalCore.Process questionWorld.toCausalWorld) :
    HEq (process.generate
      (show questionWorld.toCausalWorld.Current from
        (.finite questionVisit))).toLedgerReadout.wholeLedgerWriteBack
      (questionWorld.toLedgerRoot.generatedLedgerAt questionVisit.current) :=
  questionWorld.process_generate_wholeLedger_eq_canonical process
    (.finite questionVisit)

/-- The root causal carrier itself fixes every candidate to the canonical
temporal token. -/
theorem any_root_candidate_is_intrinsically_canonical
    (candidate : SourceNativeRootCausalEvolutionAt
      questionWorld (.finite questionVisit)) :
    candidate = questionWorld.authoritativeEvolutionAt
      (.finite questionVisit) :=
  candidate.eq_canonical

/-- Faithful presentation changes neither the exact occurrence nor its causal
prefix texture. -/
theorem causal_process_recovers_root_prior_trace :
    (((questionWorld.canonicalCausalFaithfulRealization).occurrencePresentation
        (show questionWorld.toCausalWorld.Current from
          causalVisit)).invFun
      (causalProcess.emitted
        (show questionWorld.toCausalWorld.Current from
          causalVisit))).toLedgerReadout.priorPatches =
        questionWorld.toLedgerRoot.generatedTemporalPriorPatchesAt
          causalVisit.history :=
  questionWorld.faithful_emitted_priorPatches_eq_root
    questionWorld.canonicalCausalFaithfulRealization
    causalVisit

/-! ## Complete-source causal identity -/

def falseSourceCausalProcess :
    CausalCore.Process (boolWorld false).toCausalWorld :=
  (boolWorld false).canonicalCausalProcess

def trueSourceCausalProcess :
    CausalCore.Process (boolWorld true).toCausalWorld :=
  (boolWorld true).canonicalCausalProcess

/-- A shared lower ledger cannot retype one source process as its sibling. -/
theorem sibling_source_process_cannot_be_reused : True := by
  fail_if_success
    exact (falseSourceCausalProcess :
      CausalCore.Process (boolWorld true).toCausalWorld)
  trivial

def falseSourceCausalFaithful : CausalCore.FaithfulRealization
    (boolWorld false).toCausalWorld falseSourceCausalProcess :=
  (boolWorld false).canonicalCausalFaithfulRealization

def trueSourceCausalFaithful : CausalCore.FaithfulRealization
    (boolWorld true).toCausalWorld trueSourceCausalProcess :=
  (boolWorld true).canonicalCausalFaithfulRealization

/-- Faithful realization retains the complete source identity. -/
theorem sibling_source_faithful_realization_cannot_be_reused : True := by
  fail_if_success
    exact (falseSourceCausalFaithful : CausalCore.FaithfulRealization
      (boolWorld true).toCausalWorld trueSourceCausalProcess)
  trivial

/- Raw ledger roots retain temporal compiler readouts, but cannot mint a
causal world or no-suspended-magic process before event-inventory admission. -/
/-- error: Invalid field `toCausalWorld` -/
#guard_msgs (substring := true) in
#check questionWorld.toLedgerRoot.toCausalWorld

/-- error: Invalid field `noSuspendedCausalMagic` -/
#guard_msgs (substring := true) in
#check questionWorld.toLedgerRoot.noSuspendedCausalMagic

def livingQuestionWorld :=
  questionWorld.toLivingWithoutFaithfulTerminal (fun _current => by
    change IsEmpty PEmpty
    infer_instance)

def livingQuestionVisit : SourceNativeTemporalVisitAt
    livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingQuestionWorld.toAuthoritativeRoot.toRoot.initialVisit

def livingQuestionOccurrence : SourceNativeTemporalVisitGeneratedEvolutionAt
    livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot livingQuestionVisit :=
  livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    livingQuestionVisit

def rawQuestionWorld : SourceNativeLivingRawWorld
    SourceNativeLedgerCompilerRegression.N
    SourceNativeLedgerCompilerRegression.V where
  source := livingQuestionWorld.source
  emitted := livingQuestionWorld.emitted

theorem rawQuestionCommuting :
    SourceNativeLivingRootCommutingAt rawQuestionWorld where
  compiler_commutes := livingQuestionWorld.compiler_commutes

/-- Removing the closure proof and regenerating it from the positive
commuting square recovers the existing living root exactly. -/
theorem raw_representation_recovers_living_root :
    rawQuestionWorld.toLivingRoot rawQuestionCommuting = livingQuestionWorld :=
  rfl

/-- A second proof of the same closure condition cannot create a sibling
world. -/
theorem raw_closure_witness_cannot_fork
    (other : SourceNativeLivingRootCommutingAt rawQuestionWorld) :
    rawQuestionWorld.toLivingRoot other = livingQuestionWorld :=
  (rawQuestionWorld.toLivingRoot_eq other rawQuestionCommuting).trans
    raw_representation_recovers_living_root

def rawCanonicalRepresentation :=
  rawQuestionWorld.canonicalRepresentation rawQuestionCommuting

def livingCausalProcess :
    CausalCore.Process livingQuestionWorld.toAnswerNextCausalWorld :=
  livingQuestionWorld.canonicalAnswerNextCausalProcess

/-- A candidate living evolution is already the zero-field canonical token. -/
theorem any_living_root_candidate_is_intrinsically_canonical
    (candidate : SourceNativeLivingRootCausalEvolutionAt livingQuestionWorld
      (ULift.up livingQuestionVisit)) :
    candidate = livingQuestionWorld.canonicalCausalAnswerAndNext
      (ULift.up livingQuestionVisit) :=
  candidate.eq_canonical

/-- The representation theorem now reaches the complete living result,
including the source-fixed next current. -/
theorem living_causal_process_generates_answerAndNext :
    livingCausalProcess.generate (ULift.up livingQuestionVisit) =
      livingQuestionWorld.canonicalCausalAnswerAndNext
        (ULift.up livingQuestionVisit) :=
  livingQuestionWorld.process_generate_eq_answerAndNext livingCausalProcess
    livingQuestionVisit

/-- Exact event identity is retained at the answer-and-next mouth. -/
theorem living_causal_process_recovers_root_occurrence :
    ((CausalCore.FaithfulRealization.occurrencePresentation
        livingQuestionWorld.canonicalAnswerNextFaithfulRealization
        (ULift.up livingQuestionVisit)).invFun
        (livingCausalProcess.emitted (ULift.up livingQuestionVisit))) =
      livingQuestionWorld.toAnswerNextCausalWorld.emitted
        (ULift.up livingQuestionVisit) :=
  livingQuestionWorld.faithful_emitted_recovers_answerNext_occurrence
    livingQuestionWorld.canonicalAnswerNextFaithfulRealization
    livingQuestionVisit

/-- A non-identity event wrapper used to verify that representation
uniqueness is about exact event provenance, not definitional carrier
equality. -/
structure WrappedLivingCausalEventAt
    (current : livingQuestionWorld.toAnswerNextCausalWorld.Current) where
  occurrence : livingQuestionWorld.toAnswerNextCausalWorld.OccurrenceAt current

def wrappedLivingCausalProcess : CausalCore.Process
    livingQuestionWorld.toAnswerNextCausalWorld where
  EventAt := WrappedLivingCausalEventAt
  emitted := fun current =>
    ⟨livingQuestionWorld.toAnswerNextCausalWorld.emitted current⟩
  compile := fun event =>
    livingQuestionWorld.answerNextNoSuspendedCausalMagic.realize
      event.occurrence

def wrappedLivingCausalFaithfulRealization : CausalCore.FaithfulRealization
    livingQuestionWorld.toAnswerNextCausalWorld
    wrappedLivingCausalProcess where
  occurrencePresentation := fun _current =>
    { toFun := fun occurrence => ⟨occurrence⟩
      invFun := WrappedLivingCausalEventAt.occurrence
      left_inv := fun _occurrence => rfl
      right_inv := by
        intro event
        cases event
        rfl }
  emitted_commutes := fun _current => rfl
  compile_lawful := fun occurrence =>
    livingQuestionWorld.answerNextNoSuspendedCausalMagic.lawful occurrence

/-- The non-identity faithful process recovers the exact root occurrence,
the installed Boolean face, and the source-generated living successor in one
factorization. -/
theorem wrappedLivingSubsystemFactorization :
    ((wrappedLivingCausalFaithfulRealization.occurrencePresentation
        (ULift.up livingQuestionVisit)).invFun
        (wrappedLivingCausalProcess.emitted
          (ULift.up livingQuestionVisit))) =
      livingQuestionWorld.toAnswerNextCausalWorld.emitted
        (ULift.up livingQuestionVisit) ∧
    wrappedLivingCausalProcess.generate (ULift.up livingQuestionVisit) =
      livingQuestionWorld.canonicalCausalAnswerAndNext
        (ULift.up livingQuestionVisit) ∧
    HEq
      ((wrappedLivingCausalProcess.generate
          (ULift.up livingQuestionVisit)).generated.projectionOutcome
        ((SourceNativeProjectionLaw.InstallationAt.refl
          livingQuestionWorld.toAuthoritativeRoot.source.projectionLaw).embed
            false))
      (livingQuestionWorld.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        false (livingQuestionWorld.emitted livingQuestionVisit.current)) ∧
    (wrappedLivingCausalProcess.generate
      (ULift.up livingQuestionVisit)).nextCurrent =
        livingQuestionWorld.generatedNextCurrentAt livingQuestionVisit :=
  rawQuestionWorld.faithfulProcess_installedSubsystemAuthority_factorizes
    rawQuestionCommuting wrappedLivingCausalFaithfulRealization
    livingQuestionVisit
    (SourceNativeProjectionLaw.InstallationAt.refl
      livingQuestionWorld.toAuthoritativeRoot.source.projectionLaw)
    false

/-- Two genuinely different event carriers realizing one raw world receive a
constructive occurrence-level presentation whose emitter and compiler both
commute. -/
def canonicalWrappedCommutingPresentation :
    CausalCore.ProcessCommutingPresentation
      livingCausalProcess wrappedLivingCausalProcess :=
  rawQuestionWorld.processes_commutingPresentation rawQuestionCommuting
    livingQuestionWorld.canonicalAnswerNextFaithfulRealization
    wrappedLivingCausalFaithfulRealization

theorem canonical_wrapped_emitter_commutes :
    (canonicalWrappedCommutingPresentation.eventPresentation
      (ULift.up livingQuestionVisit)).toFun
        (livingCausalProcess.emitted (ULift.up livingQuestionVisit)) =
      wrappedLivingCausalProcess.emitted (ULift.up livingQuestionVisit) :=
  canonicalWrappedCommutingPresentation.emitted_commutes
    (ULift.up livingQuestionVisit)

theorem canonical_wrapped_compiler_commutes :
    wrappedLivingCausalProcess.compile
        ((canonicalWrappedCommutingPresentation.eventPresentation
          (ULift.up livingQuestionVisit)).toFun
            (livingCausalProcess.emitted (ULift.up livingQuestionVisit))) =
      livingCausalProcess.compile
        (livingCausalProcess.emitted (ULift.up livingQuestionVisit)) :=
  canonicalWrappedCommutingPresentation.compile_commutes
    (livingCausalProcess.emitted (ULift.up livingQuestionVisit))

/-! A field can enter authority only through the exact occurrence
presentation.  Adding an unrelated `Bool` to an otherwise grounded singleton
event cannot inherit that authority, even though a compiler could ignore it
and return the same evolution. -/

def singletonCausalWorld : CausalCore.World where
  Current := PUnit
  OccurrenceAt := fun _current => PUnit
  EvolutionAt := fun _current => PUnit
  emitted := fun _current => PUnit.unit
  LawfulEvolutionAt := fun _occurrence _evolution => PUnit

def compositeFieldProcess : CausalCore.Process singletonCausalWorld where
  EventAt := fun _current => PUnit × Bool
  emitted := fun _current => (PUnit.unit, false)
  compile := fun _event => PUnit.unit

/-- A singleton occurrence cannot faithfully present an ungrounded Boolean
field. -/
theorem no_punit_bool_presentation
    (presentation : CausalCore.Presentation PUnit (PUnit × Bool)) : False := by
  have inverse_eq :
      presentation.invFun (PUnit.unit, false) =
        presentation.invFun (PUnit.unit, true) := by
    cases presentation.invFun (PUnit.unit, false)
    cases presentation.invFun (PUnit.unit, true)
    rfl
  have event_eq : (PUnit.unit, false) = (PUnit.unit, true) := by
    calc
      (PUnit.unit, false) =
          presentation.toFun (presentation.invFun (PUnit.unit, false)) :=
        (presentation.right_inv (PUnit.unit, false)).symm
      _ = presentation.toFun (presentation.invFun (PUnit.unit, true)) :=
        congrArg presentation.toFun inverse_eq
      _ = (PUnit.unit, true) := presentation.right_inv (PUnit.unit, true)
  have false_eq_true : false = true := congrArg Prod.snd event_eq
  exact Bool.noConfusion false_eq_true

/-- `Grounded(A)` does not imply `Grounded(A × B)`: the extra field needs its
own exact occurrence presentation. -/
theorem ungrounded_bool_field_cannot_borrow_authority :
    CausalCore.FaithfulRealization singletonCausalWorld
      compositeFieldProcess → False := by
  intro faithful
  exact no_punit_bool_presentation
    (faithful.occurrencePresentation PUnit.unit)

/-! The operational-equivalence representation has the same occurrence
discipline.  Only the compiler comparison changes from equality to the
equivalence relation already fixed by the world. -/

def livingOperationalLaw : CausalCore.NoSuspendedOperationalMagic
    livingQuestionWorld.toAnswerNextCausalWorld.toOperationalWorld :=
  livingQuestionWorld.answerNextNoSuspendedCausalMagic.toOperational

def livingOperationalCanonicalProcess : CausalCore.OperationalProcess
    livingQuestionWorld.toAnswerNextCausalWorld.toOperationalWorld :=
  livingOperationalLaw.toProcess

def livingOperationalCanonicalFaithfulRealization :
    CausalCore.OperationalFaithfulRealization
      livingQuestionWorld.toAnswerNextCausalWorld.toOperationalWorld
      livingOperationalCanonicalProcess where
  occurrencePresentation := fun _current =>
    { toFun := id
      invFun := id
      left_inv := fun _occurrence => rfl
      right_inv := fun _event => rfl }
  emitted_commutes := fun _current => rfl
  compile_lawful := fun occurrence => livingOperationalLaw.lawful occurrence

def wrappedLivingOperationalProcess : CausalCore.OperationalProcess
    livingQuestionWorld.toAnswerNextCausalWorld.toOperationalWorld where
  EventAt := WrappedLivingCausalEventAt
  emitted := fun current =>
    ⟨livingQuestionWorld.toAnswerNextCausalWorld.emitted current⟩
  compile := fun event => livingOperationalLaw.realize event.occurrence

def wrappedLivingOperationalFaithfulRealization :
    CausalCore.OperationalFaithfulRealization
      livingQuestionWorld.toAnswerNextCausalWorld.toOperationalWorld
      wrappedLivingOperationalProcess where
  occurrencePresentation := fun _current =>
    { toFun := fun occurrence => ⟨occurrence⟩
      invFun := WrappedLivingCausalEventAt.occurrence
      left_inv := fun _occurrence => rfl
      right_inv := by
        intro event
        cases event
        rfl }
  emitted_commutes := fun _current => rfl
  compile_lawful := fun occurrence => livingOperationalLaw.lawful occurrence

def operationalCanonicalWrappedCommutingPresentation :
    CausalCore.OperationalProcessCommutingPresentation
      livingOperationalCanonicalProcess wrappedLivingOperationalProcess :=
  livingOperationalCanonicalFaithfulRealization.commutingPresentation
    livingOperationalLaw wrappedLivingOperationalFaithfulRealization

def compositeOperationalFieldProcess : CausalCore.OperationalProcess
    singletonCausalWorld.toOperationalWorld where
  EventAt := fun _current => PUnit × Bool
  emitted := fun _current => (PUnit.unit, false)
  compile := fun _event => PUnit.unit

/-- Operational equivalence cannot make an ungrounded field contagious: the
event carrier still has to present the exact occurrence inventory. -/
theorem operational_ungrounded_bool_field_cannot_borrow_authority :
    CausalCore.OperationalFaithfulRealization
      singletonCausalWorld.toOperationalWorld
      compositeOperationalFieldProcess → False := by
  intro faithful
  exact no_punit_bool_presentation
    (faithful.occurrencePresentation PUnit.unit)

/-! The root-local representation above intentionally ends at an
authoritative next current.  Global continuation authority is indexed by one
fixed source process, which retains the complete next living law. -/

def livingSourceProcessCausalProcess : CausalCore.Process
    RootAnswerNextHistoryRegression.process.toAnswerNextCausalWorld :=
  RootAnswerNextHistoryRegression.process.canonicalAnswerNextCausalProcess

/-- The zero-field evolution carrier fixes the full source-process successor. -/
theorem any_source_process_candidate_is_intrinsically_canonical
    (candidate : SourceNativeLivingProcessCausalEvolutionAt
      RootAnswerNextHistoryRegression.process (ULift.up none)) :
    candidate =
      RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext
        (ULift.up none) :=
  candidate.eq_canonical

/-- A fixed source process generates one complete answer and its exact next
process state. -/
theorem living_source_process_generates_full_answerAndNext :
    livingSourceProcessCausalProcess.generate (ULift.up none) =
      RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext
        (ULift.up none) :=
  RootAnswerNextHistoryRegression.process.process_generate_eq_answerAndNext
    livingSourceProcessCausalProcess
    none

/-- The next living source law is a derived readout of the fixed process
state.  It is not recovered by erasing the target to an authoritative root. -/
theorem living_source_process_retains_full_next_law :
    (livingSourceProcessCausalProcess.generate
      (ULift.up none)).nextCurrent =
      RootAnswerNextHistoryRegression.process.stateAt
        (RootAnswerNextHistoryRegression.process.successor none) :=
  RootAnswerNextHistoryRegression.process.process_nextCurrent_eq_source
    livingSourceProcessCausalProcess
    none

/-- Across a process step, the installed face, exact temporal occurrence and
full next living current remain one compiler image.  Recanonicalizing a later
carrier cannot retroactively choose a different face for this row. -/
theorem living_source_process_installed_face_factorizes :
    let current : SourceNativeLivingProcessCausalCurrentAt
        RootAnswerNextHistoryRegression.process := ULift.up (some 0)
    let evolution :=
      RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext current
    evolution.generated =
        livingWriteRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          (writeTemporalVisit 0) ∧
      HEq (evolution.generated.projectionOutcome ())
        (livingWriteRoot.toAuthoritativeRoot.projectionOutcomeAt ()
          (writeTemporalVisit 0).current) ∧
      evolution.nextCurrent =
        RootAnswerNextHistoryRegression.process.stateAt (some 1) := by
  dsimp only
  exact
    (RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext
      (ULift.up (some 0))).installedSubsystemAuthority_factorizes
        (SourceNativeProjectionLaw.InstallationAt.refl
          livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
        ()

/-- Even an arbitrary faithful executor of the complete process must recover
the same process-state occurrence, face and successor. -/
theorem living_source_process_faithful_executor_factorizes :
    let sourceProcess := RootAnswerNextHistoryRegression.process
    let current : SourceNativeLivingProcessCausalCurrentAt sourceProcess :=
      ULift.up (some 0)
    ((sourceProcess.canonicalAnswerNextFaithfulRealization
        |>.occurrencePresentation current).invFun
          (sourceProcess.canonicalAnswerNextCausalProcess.emitted current)) =
        sourceProcess.toAnswerNextCausalWorld.emitted current ∧
      sourceProcess.canonicalAnswerNextCausalProcess.generate current =
        sourceProcess.canonicalCausalAnswerAndNext current ∧
      HEq
        ((sourceProcess.canonicalAnswerNextCausalProcess.generate current)
          |>.generated.projectionOutcome ())
        (livingWriteRoot.toAuthoritativeRoot.projectionOutcomeAt ()
          (writeTemporalVisit 0).current) ∧
      (sourceProcess.canonicalAnswerNextCausalProcess.generate current).nextCurrent =
        sourceProcess.stateAt (some 1) := by
  dsimp only
  exact
    SourceNativeLivingRootProcess.faithfulProcess_installedSubsystemAuthority_factorizes
      RootAnswerNextHistoryRegression.process
      RootAnswerNextHistoryRegression.process.canonicalAnswerNextFaithfulRealization
      (some 0)
      (SourceNativeProjectionLaw.InstallationAt.refl
        livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
      ()

/-- A faithful process executor cannot ground one component and smuggle a
second component across the next-state seam.  Both installed coordinates are
read at the same exact process occurrence. -/
theorem living_source_process_faithful_joint_executor_factorizes :
    let sourceProcess := RootAnswerNextHistoryRegression.process
    let current : SourceNativeLivingProcessCausalCurrentAt sourceProcess :=
      ULift.up (some 0)
    ((sourceProcess.canonicalAnswerNextFaithfulRealization
        |>.occurrencePresentation current).invFun
          (sourceProcess.canonicalAnswerNextCausalProcess.emitted current)) =
        sourceProcess.toAnswerNextCausalWorld.emitted current ∧
      sourceProcess.canonicalAnswerNextCausalProcess.generate current =
        sourceProcess.canonicalCausalAnswerAndNext current ∧
      HEq
        ((sourceProcess.canonicalAnswerNextCausalProcess.generate current)
          |>.generated.installedJointFaceReadout
            (SourceNativeProjectionLaw.InstallationAt.refl
              livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
            (SourceNativeProjectionLaw.InstallationAt.refl
              livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
            () ()).1
        (livingWriteRoot.toAuthoritativeRoot.projectionOutcomeAt ()
          (writeTemporalVisit 0).current) ∧
      HEq
        ((sourceProcess.canonicalAnswerNextCausalProcess.generate current)
          |>.generated.installedJointFaceReadout
            (SourceNativeProjectionLaw.InstallationAt.refl
              livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
            (SourceNativeProjectionLaw.InstallationAt.refl
              livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
            () ()).2
        (livingWriteRoot.toAuthoritativeRoot.projectionOutcomeAt ()
          (writeTemporalVisit 0).current) ∧
      (sourceProcess.canonicalAnswerNextCausalProcess.generate current).nextCurrent =
        sourceProcess.stateAt (some 1) := by
  dsimp only
  exact
    SourceNativeLivingRootProcess.faithfulProcess_installedJointSubsystemAuthority_factorizes
      RootAnswerNextHistoryRegression.process
      RootAnswerNextHistoryRegression.process.canonicalAnswerNextFaithfulRealization
      (some 0)
      (SourceNativeProjectionLaw.InstallationAt.refl
        livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
      (SourceNativeProjectionLaw.InstallationAt.refl
        livingWriteRoot.toAuthoritativeRoot.source.projectionLaw)
      () ()

/-- Even a caller-selected parameter cannot fork a fixed source process while
both selections retain the same complete registered current. -/
theorem parameter_selection_cannot_fork_answer_and_next
    (select : Bool → RootAnswerNextHistoryRegression.process.State)
    (current_eq :
      RootAnswerNextHistoryRegression.process.stateAt (select false) =
        RootAnswerNextHistoryRegression.process.stateAt (select true)) :
    RootAnswerNextHistoryRegression.process.stateAt
          (RootAnswerNextHistoryRegression.process.successor (select false)) =
        RootAnswerNextHistoryRegression.process.stateAt
          (RootAnswerNextHistoryRegression.process.successor (select true)) ∧
      HEq
        (RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext
          (ULift.up (select false)))
        (RootAnswerNextHistoryRegression.process.canonicalCausalAnswerAndNext
          (ULift.up (select true))) := by
  exact
    ⟨RootAnswerNextHistoryRegression.process
        |>.successor_current_eq_of_current_eq current_eq,
      RootAnswerNextHistoryRegression.process
        |>.canonicalAnswerAndNext_heq_of_current_eq current_eq⟩

#print axioms SourceNativeLivingRootProcess.successor_difference_reflects_current
#print axioms SourceNativeLivingRootProcess.canonicalAnswerAndNext_heq_of_current_eq
#print axioms parameter_selection_cannot_fork_answer_and_next

/-- Inquiry, answer, prior/current ledger texture, and continuation are one
root occurrence readout rather than independently supplied certificates. -/
def inquiryAnswerAndNext :=
  (livingQuestionWorld.canonicalCausalAnswerAndNext
    (ULift.up livingQuestionVisit)).inquiryAnswerAndNext false true

/- An erased ledger/history occurrence cannot recover a living successor:
the terminal-handoff source identity is no longer present in its type. -/
#guard_msgs (substring := true) in
#check livingQuestionOccurrence.inquiryAnswerAndNext false true

/-- An installed domain coordinate, its occurrence, and its successor all
factor through the same living-root compiler image. -/
theorem installed_question_authority_factorizes :
    let evolution := livingQuestionWorld.canonicalCausalAnswerAndNext
      (ULift.up livingQuestionVisit)
    ;
    evolution.generated =
        livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          livingQuestionVisit ∧
      HEq (evolution.generated.projectionOutcome false)
        (livingQuestionWorld.toAuthoritativeRoot.projectionOutcomeAt false
          livingQuestionVisit.current) ∧
      evolution.nextCurrent =
        livingQuestionWorld.generatedNextCurrentAt livingQuestionVisit := by
  exact (livingQuestionWorld.canonicalCausalAnswerAndNext
    (ULift.up livingQuestionVisit)).installedSubsystemAuthority_factorizes
      (SourceNativeProjectionLaw.InstallationAt.refl
        livingQuestionWorld.toAuthoritativeRoot.source.projectionLaw)
      false

/-- The ledger readout and exact source compiler output are the same generated
account. -/
theorem realized_ledger_is_source_compiler_image :
    HEq realized.wholeLedgerWriteBack
      (questionWorld.toLedgerRoot.generatedLedgerAt questionVisit.current) :=
  realized.wholeLedgerWriteBack_eq

/-- Two distinct source-law coordinates are read directly on the same exact
temporal occurrence.  No global domain-name dictionary or pair carrier is
interposed. -/
theorem realized_projection_outcomes_are_exact_root_faces :
    HEq (realized.projectionOutcome false)
        (questionWorld.projectionOutcomeAt false questionVisit.current) ∧
      HEq (realized.projectionOutcome true)
        (questionWorld.projectionOutcomeAt true questionVisit.current) :=
  ⟨realized.projectionOutcome_heq_sourceOutcome false,
    realized.projectionOutcome_heq_sourceOutcome true⟩

/-- Cross-domain visibility is one coface readout, not an A-to-B bridge. -/
theorem realized_joint_face_readout_is_exact_root_coface :
    HEq (realized.jointFaceReadout false true).1
        (questionWorld.projectionOutcomeAt false questionVisit.current) ∧
      HEq (realized.jointFaceReadout false true).2
        (questionWorld.projectionOutcomeAt true questionVisit.current) :=
  realized.jointFaceReadout_heq_sourceOutcomes false true

def singletonQuestionComponent (answer : Bool) :
    SourceNativeProjectionLaw
      livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Bool
  project := fun _ {_} _ _ => answer

def falseQuestionInstallation : SourceNativeProjectionLaw.InstallationAt
    (singletonQuestionComponent false) questionProjectionLaw where
  embed := fun _ => false
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    unfold SourceNativeProjectionLaw.outcomeAt questionProjectionLaw
      singletonQuestionComponent
    rfl

def trueQuestionInstallation : SourceNativeProjectionLaw.InstallationAt
    (singletonQuestionComponent true) questionProjectionLaw where
  embed := fun _ => true
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    unfold SourceNativeProjectionLaw.outcomeAt questionProjectionLaw
      singletonQuestionComponent
    rfl

/-- A caller cannot present the `false` component through the `true` root
coordinate.  The component and whole-law payload types coincide, so this is
the hostile case where a wrapper could otherwise hide the changed bit solely
in its embedding. -/
theorem false_component_cannot_install_at_true_coordinate
    (installation : SourceNativeProjectionLaw.InstallationAt
      (singletonQuestionComponent false) questionProjectionLaw)
    (embed_eq : installation.embed () = true) : False := by
  have outcome_heq := installation.outcome_heq
    (livingQuestionWorld.emitted livingQuestionVisit.current) ()
  rw [embed_eq] at outcome_heq
  have concrete_outcome_heq :
      HEq (Sum.inl ⟨(), true⟩ : (Sigma fun _ : Unit => Bool) ⊕ PEmpty)
        (Sum.inl ⟨(), false⟩ : (Sigma fun _ : Unit => Bool) ⊕ PEmpty) := by
    dsimp [SourceNativeProjectionLaw.outcomeAt, questionProjectionLaw,
      singletonQuestionComponent] at outcome_heq
    exact outcome_heq
  have outcome_eq : Sum.inl ⟨(), true⟩ =
      (Sum.inl ⟨(), false⟩ : (Sigma fun _ : Unit => Bool) ⊕ PEmpty) :=
    eq_of_heq concrete_outcome_heq
  have pair_eq : (⟨(), true⟩ : Sigma fun _ : Unit => Bool) =
      ⟨(), false⟩ := Sum.inl.inj outcome_eq
  have payload_eq : true = false := congrArg Sigma.snd pair_eq
  exact Bool.noConfusion payload_eq

/-- Any two installed presentations of one component agree on the full
dependent root outcome, even when their embedding functions are not
definitionally equal. -/
theorem duplicate_component_installations_cannot_change_outcome
    (left right : SourceNativeProjectionLaw.InstallationAt
      (singletonQuestionComponent false) questionProjectionLaw) :
    HEq
      (questionProjectionLaw.outcomeAt (left.embed ())
        (livingQuestionWorld.emitted livingQuestionVisit.current))
      (questionProjectionLaw.outcomeAt (right.embed ())
        (livingQuestionWorld.emitted livingQuestionVisit.current)) :=
  left.outcome_heq_of_same_component right
    (livingQuestionWorld.emitted livingQuestionVisit.current) ()

/-- Independently presented Boolean components retain their exact outcomes
when read together on the living root coface. -/
theorem installed_question_answer_components_factorize_together :
    let evolution := livingQuestionWorld.canonicalCausalAnswerAndNext
      (ULift.up livingQuestionVisit)
    evolution.generated =
        livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          livingQuestionVisit ∧
      HEq
        (evolution.generated.installedJointFaceReadout
          falseQuestionInstallation trueQuestionInstallation () ()).1
        ((singletonQuestionComponent false).outcomeAt ()
          (livingQuestionWorld.emitted livingQuestionVisit.current)) ∧
      HEq
        (evolution.generated.installedJointFaceReadout
          falseQuestionInstallation trueQuestionInstallation () ()).2
        ((singletonQuestionComponent true).outcomeAt ()
          (livingQuestionWorld.emitted livingQuestionVisit.current)) ∧
      evolution.nextCurrent =
        livingQuestionWorld.generatedNextCurrentAt livingQuestionVisit := by
  exact (livingQuestionWorld.canonicalCausalAnswerAndNext
    (ULift.up livingQuestionVisit)).installedJointSubsystemAuthority_factorizes
      falseQuestionInstallation trueQuestionInstallation () ()

#print axioms SourceNativeProjectionLaw.InstallationAt.outcome_heq_of_same_component
#print axioms false_component_cannot_install_at_true_coordinate
#print axioms duplicate_component_installations_cannot_change_outcome

/-- A non-identity faithful event presentation preserves two genuinely
different installed component outcomes as one root coface. -/
theorem wrapped_living_joint_components_factorize_together :
    ((wrappedLivingCausalFaithfulRealization.occurrencePresentation
        (ULift.up livingQuestionVisit)).invFun
        (wrappedLivingCausalProcess.emitted
          (ULift.up livingQuestionVisit))) =
      livingQuestionWorld.toAnswerNextCausalWorld.emitted
        (ULift.up livingQuestionVisit) ∧
    wrappedLivingCausalProcess.generate (ULift.up livingQuestionVisit) =
      livingQuestionWorld.canonicalCausalAnswerAndNext
        (ULift.up livingQuestionVisit) ∧
    HEq
      ((wrappedLivingCausalProcess.generate
          (ULift.up livingQuestionVisit)).generated.installedJointFaceReadout
        falseQuestionInstallation trueQuestionInstallation () ()).1
      ((singletonQuestionComponent false).outcomeAt ()
        (livingQuestionWorld.emitted livingQuestionVisit.current)) ∧
    HEq
      ((wrappedLivingCausalProcess.generate
          (ULift.up livingQuestionVisit)).generated.installedJointFaceReadout
        falseQuestionInstallation trueQuestionInstallation () ()).2
      ((singletonQuestionComponent true).outcomeAt ()
        (livingQuestionWorld.emitted livingQuestionVisit.current)) ∧
    (wrappedLivingCausalProcess.generate
      (ULift.up livingQuestionVisit)).nextCurrent =
        livingQuestionWorld.generatedNextCurrentAt livingQuestionVisit :=
  rawQuestionWorld.faithfulProcess_installedJointSubsystemAuthority_factorizes
    rawQuestionCommuting wrappedLivingCausalFaithfulRealization
    livingQuestionVisit falseQuestionInstallation trueQuestionInstallation
    () ()

/-- The full temporal occurrence has no observer kernel for any downstream
consumer.  Only a proper restriction can hide a generated distinction. -/
theorem realized_root_coface_has_no_hidden_null
    (consumer : ExactTemporalCausalRootEvent questionWorld.toLedgerRoot -> Bool) :
    IsEmpty (HiddenNullWitness
      (@rootCofaceRead _ _ questionWorld.toLedgerRoot) consumer) :=
  no_hiddenNull_at_rootCofaceRead consumer

/-- Two readouts at one fixed source occurrence cannot change either the
occurrence or its whole-ledger write-back. -/
theorem fixed_source_event_has_one_temporal_realization
    (left right :
      SourceNativeTemporalVisitGeneratedEvolutionAt
        questionWorld.toLedgerRoot (.finite questionVisit)) :
    left.occurrence = right.occurrence ∧
      HEq left.wholeLedgerWriteBack right.wholeLedgerWriteBack :=
  ⟨left.occurrence_eq.trans right.occurrence_eq.symm,
    left.wholeLedgerWriteBack_eq.trans
      right.wholeLedgerWriteBack_eq.symm⟩

end RootCoreRepresentationRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
