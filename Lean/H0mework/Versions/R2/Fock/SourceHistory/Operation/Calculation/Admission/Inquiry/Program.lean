import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry

open SourceOperationEffects RootInquiryCompletion
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

namespace Unit
export RootGeneratedDebtActivationJointSource.Unit (finiteVisit temporalVisit sourceRow)
end Unit

variable (runtime : LivingRuntimeState process)

def sourceVisit : SourceNativeTemporalVisitAt (sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot :=
  Target.sourceVisit runtime

def sourceEntry : OpenResponsibilityAt OldN
    ((sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((sourceRoot runtime).emitted (sourceVisit runtime).current)) := Target.sourceEntry runtime

private def sourceInitialRow :
    ((sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (sourceRoot runtime).toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      (CanonicalUnitArithmeticRoot.rootLedgerEntry (sourceRoot runtime).toAuthoritativeRoot.toRoot.source.initial) :=
  (((sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite (sourceRoot runtime).toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
      (CanonicalUnitArithmeticRoot.rootLedgerEntry
        (sourceRoot runtime).toAuthoritativeRoot.toRoot.source.initial)).get (by rfl)

private def sourceAuthorityAt (depth : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (sourceRoot runtime) (temporalVisit depth)
      (CanonicalUnitArithmeticRoot.rootLedgerEntry (finiteVisit depth).current) := by
  cases depth with
  | zero => exact .generatedFromInitialRow (sourceRoot runtime) _ (sourceInitialRow runtime)
  | succ depth =>
      have previous := sourceAuthorityAt depth
      have next := previous.next (by rfl)
      have entryEq := CanonicalUnitArithmeticRoot.rootLedgerEntry_unique
        (finiteVisit (depth + 1)).current
        ((sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
          (CanonicalUnitArithmeticRoot.rootLedgerEntry (finiteVisit depth).current))
      exact entryEq ▸ next

def sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (sourceRoot runtime) (sourceVisit runtime) (sourceEntry runtime) := sourceAuthorityAt runtime runtime.state

def sourceProjection : (sourceRoot runtime).source.base.projectionLaw.Projection →
    (targetRoot runtime).source.base.projectionLaw.Projection
  | .component query => (targetSourceTokenInstallation runtime).embed query
  | .inherited old => (targetOldInstallation runtime).embed (oldProjection runtime old)

theorem sourceProjection_injective : Function.Injective (sourceProjection runtime) := by
  intro first second same
  cases first with
  | component first =>
      cases second with
      | component second =>
          have pair := (targetSourceTokenInstallation runtime).embed_injective same
          exact congrArg SourceNativeProjectionCoface.component pair
      | inherited second => cases same
  | inherited first =>
      cases second with
      | component second => cases same
      | inherited second =>
          have pair := (oldProjection_injective runtime) ((targetOldInstallation runtime).embed_injective same)
          exact congrArg SourceNativeProjectionCoface.inherited pair

private theorem targetOldToken_outcome {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current) (querySeal : PUnit) :
    HEq ((targetOldTokenLaw runtime).outcomeAt querySeal occurrence)
      ((sourceTokenLaw runtime).outcomeAt querySeal (Joint.originalOccurrence (registered runtime) occurrence)) := by
  cases querySeal
  rfl

theorem sourceOutcome_heq (projection : (sourceRoot runtime).source.base.projectionLaw.Projection) :
    HEq ((targetRoot runtime).source.base.projectionLaw.outcomeAt (sourceProjection runtime projection)
      (initialOccurrence runtime))
      ((sourceRoot runtime).source.base.projectionLaw.outcomeAt projection runtime.emittedOccurrence) := by
  cases projection with
  | component query =>
      have same := targetOldToken_outcome runtime (initialOccurrence runtime) query
      rw [original_initial_occurrence] at same
      exact ((targetSourceTokenInstallation runtime).outcome_heq (initialOccurrence runtime) query).trans
        (same.trans ((sourceTokenInstallation runtime).outcome_heq runtime.emittedOccurrence query).symm)
  | inherited old =>
      exact ((targetOldInstallation runtime).outcome_heq (initialOccurrence runtime) (oldProjection runtime old)).trans
        ((initial_oldOutcome_heq runtime old).trans
          ((sourceOldInstallation runtime).outcome_heq runtime.emittedOccurrence old).symm)

/-- Only the complete source epoch changes; the actual raw input, step, patch
and first successor are reused from the already generated target. -/
def targetAt (event : ExactTemporalCausalRootEventAt
    (sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot (sourceVisit runtime)) :
    SourceNativeDebtAdmissionActualActionTargetAt (sourceRoot runtime) (sourceVisit runtime) event
      (sourceEntry runtime) (sourceAuthority runtime) where
  law := (Target.targetAt runtime event).law
  sourceState := (Target.targetAt runtime event).sourceState
  stepEvent := (Target.targetAt runtime event).stepEvent
  sourceSuccessor := (Target.targetAt runtime event).sourceSuccessor
  TargetV := (Target.targetAt runtime event).TargetV
  targetRoot := targetRoot runtime
  initialSupport_eq := (Target.targetAt runtime event).initialSupport_eq
  initialOldRow := (Target.targetAt runtime event).initialOldRow
  initialBornRow := (Target.targetAt runtime event).initialBornRow
  firstSuccessor := (Target.targetAt runtime event).firstSuccessor
  firstSupport_eq := (Target.targetAt runtime event).firstSupport_eq
  firstDestination_heq := (Target.targetAt runtime event).firstDestination_heq
  oldProjection := sourceProjection runtime
  oldProjection_injective := sourceProjection_injective runtime
  oldOutcome_heq := sourceOutcome_heq runtime
  canonical_targetNextVisit_eq := by
    apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
    rfl
  Answer := (Target.targetAt runtime event).Answer
  answer := (Target.targetAt runtime event).answer
  Receipt := (Target.targetAt runtime event).Receipt
  receipt := (Target.targetAt runtime event).receipt

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (sourceRoot runtime) (sourceVisit runtime)
    (sourceEntry runtime) (sourceAuthority runtime) where
  targetAt := targetAt runtime

def sourceEvent := (sourceRoot runtime).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (sourceVisit runtime)

def birthGenerated := (birthProgram runtime).generate (sourceEvent runtime)

def birthCompilation : SourceNativeInquiryCompilationProgramAt (sourceRoot runtime) (sourceVisit runtime)
    oldU7 oldCalculus (TheoryState.rootSemantic OldN) PUnit.unit (ULift.up.{1, 0} runtime.emittedOccurrence)
      (sourceEntry runtime) (sourceAuthority runtime) where
  compile := fun event => .debtAdmission ((birthProgram runtime).generate event)

def birthState : RootInquiryStateAt OldN CanonicalUnitArithmeticRoot.V where
  root := sourceRoot runtime
  visit := sourceVisit runtime
  U7 := oldU7
  calculus := oldCalculus
  Query := PUnit
  entryAt := fun _ => sourceEntry runtime
  authorityAt := fun _ => sourceAuthority runtime
  compilationProgramAt := fun query => by cases query; exact birthCompilation runtime
  compilationFaceAt := fun query => by
    cases query
    exact
      { projection := (sourceTokenInstallation runtime).embed PUnit.unit
        active := PUnit.unit
        classifier_eq := rfl
        project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ obstruction
    exact nomatch obstruction

def birthPresentation : RootInquiryStatePresentation where
  N := OldN
  V := CanonicalUnitArithmeticRoot.V
  state := .create (birthState runtime)

theorem birth_compiles : (birthState runtime).compileInquiry PUnit.unit = .debtAdmission (birthGenerated runtime) := rfl

def mathCurrent (depth : Nat) : Joint.Current (registered runtime) :=
  (Unit.finiteVisit (registered runtime) (depth + 1)).current

def mathVisit (depth : Nat) : SourceNativeTemporalVisitAt (targetRoot runtime).toAuthoritativeRoot.toLedgerRoot :=
  Unit.temporalVisit (registered runtime) (depth + 1)

def mathEntry (depth : Nat) := Unit.sourceRow (registered runtime) (mathCurrent runtime depth) 1

private def mathInitialRow :
    ((targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetRoot runtime).toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      (Unit.sourceRow (registered runtime) (initialCurrent runtime) 1) :=
  (((targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite (targetRoot runtime).toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
      (Unit.sourceRow (registered runtime) (initialCurrent runtime) 1)).get (by rfl)

private def mathAuthorityAt (depth : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (targetRoot runtime)
      (Unit.temporalVisit (registered runtime) depth)
      (Unit.sourceRow (registered runtime) (Unit.finiteVisit (registered runtime) depth).current 1) := by
  cases depth with
  | zero => exact .generatedFromInitialRow (targetRoot runtime) _ (mathInitialRow runtime)
  | succ depth =>
      have previous := mathAuthorityAt depth
      have next := previous.next (by rfl)
      have entryEq :
          (targetRoot runtime).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
              (Unit.sourceRow (registered runtime) (Unit.finiteVisit (registered runtime) depth).current 1) =
            Unit.sourceRow (registered runtime) (Unit.finiteVisit (registered runtime) (depth + 1)).current 1 := by
        change RootGeneratedDebtActivationJointSource.Unit.targetRow (registered runtime)
          (Unit.finiteVisit (registered runtime) depth).current
          ((RootGeneratedDebtActivationJointSource.Unit.rowInventory (registered runtime)
            (Unit.finiteVisit (registered runtime) depth).current).backward
            ((RootGeneratedDebtActivationJointSource.Unit.rowInventory (registered runtime)
              (Unit.finiteVisit (registered runtime) depth).current).forward 1)) = _
        rw [(RootGeneratedDebtActivationJointSource.Unit.rowInventory (registered runtime)
          (Unit.finiteVisit (registered runtime) depth).current).backward_forward]
        exact RootGeneratedDebtActivationJointSource.Unit.targetRow_inventory
          (registered runtime) (Unit.finiteVisit (registered runtime) depth).current 1
      exact entryEq ▸ next

def mathAuthority (depth : Nat) : SourceNativeLivingTemporalCausalEntryAuthorityAt (targetRoot runtime)
    (mathVisit runtime depth) (mathEntry runtime depth) := mathAuthorityAt runtime (depth + 1)

def mathAnswerFace (depth : Nat) : SourceNativeRootSemanticFaceAt (targetRoot runtime) (mathVisit runtime depth) where
  projection := (targetOldInstallation runtime).embed (mathProjection runtime)
  active := PUnit.unit
  classifier_eq := rfl

def mathConsumer (depth : Nat) : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{1, 0} ((targetRoot runtime).emitted (mathCurrent runtime depth)))
      (mathEntry runtime depth) (mathAnswerFace runtime depth) where
  projection := (targetConsumerInstallation runtime).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def mathCompilation (depth : Nat) : SourceNativeInquiryCompilationProgramAt (targetRoot runtime) (mathVisit runtime depth)
    (newU7 runtime) (newCalculus runtime) (TheoryState.rootSemantic (NewN runtime)) PUnit.unit
      (ULift.up.{1, 0} ((targetRoot runtime).emitted (mathCurrent runtime depth)))
      (mathEntry runtime depth) (mathAuthority runtime depth) where
  compile := fun _event => .answered (mathAnswerFace runtime depth) (mathConsumer runtime depth)

def mathState (depth : Nat) : RootInquiryStateAt (NewN runtime) (Joint.JointV (registered runtime)) where
  root := targetRoot runtime
  visit := mathVisit runtime depth
  U7 := newU7 runtime
  calculus := newCalculus runtime
  Query := PUnit
  entryAt := fun _ => mathEntry runtime depth
  authorityAt := fun _ => mathAuthority runtime depth
  compilationProgramAt := fun query => by cases query; exact mathCompilation runtime depth
  compilationFaceAt := fun query => by
    cases query
    exact
      { projection := (targetCompilationInstallation runtime).embed PUnit.unit
        active := PUnit.unit
        classifier_eq := rfl
        project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ obstruction
    cases obstruction with
    | inl impossible => exact nomatch impossible
    | inr impossible => exact nomatch impossible

def mathPresentation (depth : Nat) : RootInquiryStatePresentation where
  N := NewN runtime
  V := Joint.JointV (registered runtime)
  state := .create (mathState runtime depth)

theorem math_compiles (depth : Nat) : (mathState runtime depth).compileInquiry PUnit.unit =
    .answered (mathAnswerFace runtime depth) (mathConsumer runtime depth) := rfl

end
end SourcePhysicalCalculationAdmission.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
