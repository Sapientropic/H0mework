import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Authority

/-! Exact source history admits the complete born source and its actual
first successor. No target-side authority or coverage is supplied. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission
namespace Target

open SourceOperationEffects SourcePhysicalCalculation
open DebtActivationWorld DebtActivationLedger RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev sourceRoot := NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.livingRoot

def sourceVisit (runtime : LivingRuntimeState process) :
    SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot := runtime.current.visit

def sourceEntry (runtime : LivingRuntimeState process) :
    OpenResponsibilityAt CanonicalUnitArithmeticRoot.N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted (sourceVisit runtime).current)) :=
  CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime)

private def initialSourceRow :
    (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite sourceRoot.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      (CanonicalUnitArithmeticRoot.rootLedgerEntry sourceRoot.toAuthoritativeRoot.toRoot.source.initial) :=
  ((sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite sourceRoot.toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
    (CanonicalUnitArithmeticRoot.rootLedgerEntry sourceRoot.toAuthoritativeRoot.toRoot.source.initial)).get (by rfl)

private def finiteSourceAuthority (depth : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot (temporalVisit depth)
      (CanonicalUnitArithmeticRoot.rootLedgerEntry (finiteVisit depth).current) := by
  cases depth with
  | zero =>
      exact .generatedFromInitialRow sourceRoot
        (CanonicalUnitArithmeticRoot.rootLedgerEntry sourceRoot.toAuthoritativeRoot.toRoot.source.initial)
        initialSourceRow
  | succ depth =>
      have previous := finiteSourceAuthority depth
      have next := previous.next (by rfl)
      have entryEq := CanonicalUnitArithmeticRoot.rootLedgerEntry_unique
        (finiteVisit (depth + 1)).current
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
          (CanonicalUnitArithmeticRoot.rootLedgerEntry (finiteVisit depth).current))
      exact entryEq ▸ next

def sourceAuthority (runtime : LivingRuntimeState process) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot (sourceVisit runtime) (sourceEntry runtime) :=
  finiteSourceAuthority runtime.state

variable (runtime : LivingRuntimeState process)

def sourceSuccessor (event : ExactTemporalCausalRootEventAt
    sourceRoot.toAuthoritativeRoot.toLedgerRoot (sourceVisit runtime)) :
    SourceNativeLedgerGeneratedSuccessorAt event.occurrence event.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? event.wholeLedgerWriteBack).get (by rfl)

def targetInitialVisit := SourceNativeTemporalVisitAt.finite
  (SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toRoot.initialVisit

def firstSuccessor :
    SourceNativeLedgerGeneratedSuccessorAt
      ((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (targetInitialVisit runtime)).occurrence
      ((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (targetInitialVisit runtime)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (targetInitialVisit runtime)).wholeLedgerWriteBack).get (by rfl)

def initialOldRow (entry : OpenResponsibilityAt CanonicalUnitArithmeticRoot.N (baseCurrent runtime)) :
    ((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (targetInitialVisit runtime)).GeneratedEntryRowAt
      (oldEntry (law := SourcePhysicalCalculationRegistered.worldLaw runtime)
        (state? := some (SourcePhysicalCalculation.initial runtime)) entry) :=
  (((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (targetInitialVisit runtime)).canonicalGeneratedEntryRow?
      (oldEntry (law := SourcePhysicalCalculationRegistered.worldLaw runtime)
        (state? := some (SourcePhysicalCalculation.initial runtime)) entry)).get (by rfl)

def initialBornRow :
    ((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (targetInitialVisit runtime)).GeneratedEntryRowAt
      (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := SourcePhysicalCalculationRegistered.worldLaw runtime)
        (baseCurrent runtime) (SourcePhysicalCalculation.initial runtime)) :=
  (((SourcePhysicalCalculationAdmission.livingRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (targetInitialVisit runtime)).canonicalGeneratedEntryRow?
      (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := SourcePhysicalCalculationRegistered.worldLaw runtime)
        (baseCurrent runtime) (SourcePhysicalCalculation.initial runtime))).get (by rfl)

def targetAt (event : ExactTemporalCausalRootEventAt
    sourceRoot.toAuthoritativeRoot.toLedgerRoot (sourceVisit runtime)) :
    SourceNativeDebtAdmissionActualActionTargetAt sourceRoot (sourceVisit runtime) event
      (sourceEntry runtime) (sourceAuthority runtime) where
  law := SourcePhysicalCalculationRegistered.worldLaw runtime
  sourceState := SourcePhysicalCalculation.initial runtime
  stepEvent := SourcePhysicalCalculationAdmission.stepEvent runtime
  sourceSuccessor := sourceSuccessor runtime event
  TargetV := Joint.JointV (registered runtime)
  targetRoot := SourcePhysicalCalculationAdmission.livingRoot runtime
  initialSupport_eq := rfl
  initialOldRow := initialOldRow runtime
  initialBornRow := initialBornRow runtime
  firstSuccessor := firstSuccessor runtime
  firstSupport_eq := by
    have same := (first_joint_next runtime).2
    exact congrArg (fun state => (baseCurrent runtime.tick.next, some state)) same
  firstDestination_heq := by
    have same := initial_patch_destination runtime
    exact (heq_of_eq same).trans (by rfl)
  oldProjection := oldProjection runtime
  oldProjection_injective := oldProjection_injective runtime
  oldOutcome_heq := initial_oldOutcome_heq runtime
  canonical_targetNextVisit_eq := by
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    exact rfl
  Answer := Joint.MathReadout (registered runtime)
  answer := Joint.mathReadout (registered runtime) (initialCurrent runtime)
  Receipt := fun result => ULift.{3, 0} (PLift
    (result.state = SourcePhysicalCalculation.initial runtime ∧
      HEq result.action (RootGeneratedDebtActivationJointSource.mathAction
        (SourcePhysicalCalculationRegistered.initialEvent runtime)) ∧
      result.value =
        ((NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix.payloadAt runtime).sourceState,
          (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix.payloadAt runtime).forcedTrace)))
  receipt := ⟨⟨⟨rfl, HEq.rfl, SourcePhysicalCalculation.raw_value runtime⟩⟩⟩

def program : SourceNativeDebtAdmissionActualActionProgramAt sourceRoot (sourceVisit runtime)
    (sourceEntry runtime) (sourceAuthority runtime) where
  targetAt := targetAt runtime

def sourceEvent := sourceRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (sourceVisit runtime)

def generated := (program runtime).generate (sourceEvent runtime)


end
end Target
end SourcePhysicalCalculationAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
