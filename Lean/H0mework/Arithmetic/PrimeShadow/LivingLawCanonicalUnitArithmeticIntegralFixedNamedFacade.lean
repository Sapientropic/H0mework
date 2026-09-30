import H0mework.Arithmetic.UnitArithmetic.DualReadouts
import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticIntegralFixedCoordinateReadout
import H0mework.Arithmetic.EulerGlobal.CofiberCofinalRigidity
import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness
import H0mework.Arithmetic.EulerAnalytic.TautologicalReadback
import H0mework.Arithmetic.EulerDerived.SolutionSpecialization
import H0mework.Arithmetic.EulerDerived.SolutionFixedCoordinate
import H0mework.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticUniversalSolutionCycleSplice

/-!
# Named facade regression of the settled integral fixed component

The arithmetic source, emitter, ledger compiler and successor are unchanged.
This file extends only the projection inventory with the generated
integral-first arithmetic settlement.  The repaired carrier retains its
source-generated diagonal unit while frozen rigidity kills only the
anti-invariant difference.

The facade is admitted to the Goldbach integration track as an arithmetic
fixedness inventory.  The same payload carries the point-free cycle row
landing, quotient-zero and successor square together with the literal
common-frame block endpoint.  Mathlib coordinate projection remains the
downstream specialization of this settled component.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticIntegralFixedNamedFacade

open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticDerivedCoordinateRegression
open CanonicalUnitArithmeticEulerDeterminantCoordinateRegression
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralZeroFiberState
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity
open CanonicalUnitArithmeticIntegralFixedCoordinateReadout
open CanonicalUnitArithmeticIntegralActionCofiberFamily
open CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity
open CanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionFixedCoordinateReadback
open CanonicalUnitArithmeticActionCofiberCyclePrimePowerSplice
open CanonicalUnitArithmeticLocalCoordinateClassCycleEvaluation
open CanonicalUnitArithmeticUniversalSolutionCycleSplice
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticUnitNormalizedCoordinateRegression
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CategoryTheory

noncomputable section

/-- Exact arithmetic fixedness payload together with the fixedness-free
common-frame endpoint splice.  Both components project to `seedOccurrence`;
no normalized point or coordinate specialization is stored here. -/
structure SettledSelfDualReadout : Type where
  private mk ::
  occurrence_projects : wholeActionCofiberFace.root = seedOccurrence
  blockCofiberOccurrence_projects :
    pairBlockGlobalActionCofiberFace.root = seedOccurrence
  blockEndpointOccurrence_projects :
    CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement.pairBlockEndpointCofiberOccurrence.map
        Prod.fst = seedOccurrence
  blockEndpointSourceReadback :
    pairBlockEndpointSourceReadback = pairBlockGlobalEndpointSection
  blockLocalActualDifference : ∀ stage,
    localPairBlockTautologicalAntiInvariantReadback stage =
      localPairBlockActualEndpointDifference stage
  tautologicalReadback : (stage : Nat) →
    (localWholeTautologicalInclusion stage).1.comp
        (CochainComplex.mappingCocone.snd
          (localWholeActionMap stage)) (add_neg_cancel (1 : ℤ)) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (LocalScalarWholeRelationComplex stage))
  tautologicalFixed : ∀ stage (value : IntegralScalarCocycleCarrier),
    localTautologicalAntiInvariantReadback stage
        (integralScalarCocycleInclusion value)
        (integralScalarCocycleInclusion_differential_zero value) = 0
  generatedUniversalOccurrenceProjects :
    generatedUniversalSolutionOccurrence.map Prod.fst = seedOccurrence
  generatedUniversalTautologicalFixed :
    ∀ stage (value : GeneratedUniversalSolutionCarrier),
      localTautologicalAntiInvariantReadback stage
          (generatedUniversalInclusion value)
          (generatedUniversalInclusion_differential_zero value) = 0
  universalSolutionTautologicalFixed :
    ∀ stage (value : UniversalSolutionKernel),
      localTautologicalAntiInvariantReadback stage
          (universalInclusion value)
          (LinearMap.mem_ker.mp value.2.1) = 0
  cyclePrimePowerLanding : ∀
    (point : localIntegralUnitSingle ⟶ ScalarWholeRelationComplex)
    stage (row : FactorRow seedOccurrence.root stage),
      wholeCoordinatePointValue point stage =
        (rowPrime row : Nat) ^ rowExponent row •
          quotientCoordinatePointValue point stage row
  cycleQuotientZero : ∀
    (point : localIntegralUnitSingle ⟶ ScalarWholeRelationComplex)
    stage (row : FactorRow seedOccurrence.root stage),
      PrimePowerQuotientEvaluation.evaluator
          (LocalScalarInner stage)
          (wholeCoordinatePointValue point stage)
          (rowPrime row) (rowExponent row) = 0
  cycleSuccessor : ∀
    (point : localIntegralUnitSingle ⟶ ScalarWholeRelationComplex) stage,
      localScalarInnerSuccessor stage
          (wholeCoordinatePointValue point (stage + 1)) =
        wholeCoordinatePointValue point stage
  universalCycleFixed : ∀ stage (value : UniversalSolutionKernel),
    wholeCoordinatePointValue (universalSourcePoint value) stage = 0
  derivedSolutionRoot : blockDerivedSolutionDiagramFace.root = seedOccurrence
  mathlibDerivedPointInstalled : ∀ coordinate zetaZero,
    mathlibZeroDerivedSolutionPoint coordinate zetaZero =
      determinantLineDerivedSolutionPoint
        (mathlibZeroPoint coordinate zetaZero)
  derivedPointLeftReadback : ∀ point stage row,
    pointDerivedPointEndpointReadback point stage row
        (determinantLineDerivedSolutionPoint point) = point.pair.1
  derivedPointRightReadback : ∀ point stage row,
    pointDerivedPointEndpointReadback point stage row
        (determinantLineReversedDerivedSolutionPoint point) = point.pair.2
  diagonalUnitNonzero : globalDiagonalUnit ≠ 0
  diagonalWhole : ∀ stage dualIndex,
    wholeCoordinate seedOccurrence.root stage dualIndex
      (localValue stage globalDiagonalUnit) = 1
  diagonalQuotient : ∀ stage row,
    quotientCoordinate row (localValue stage globalDiagonalUnit) = 0

def settledSelfDualReadout : SettledSelfDualReadout where
  occurrence_projects := wholeActionCofiberFace_preserves_exact_occurrence_and_action.1
  blockCofiberOccurrence_projects :=
    pairBlockGlobalActionCofiberFace.preserves_actual_transition.1
  blockEndpointOccurrence_projects :=
    CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement.pairBlockEndpointCofiberOccurrence_projects
  blockEndpointSourceReadback := pairBlockEndpointSourceReadback_eq_section
  blockLocalActualDifference :=
    localPairBlockTautologicalAntiInvariantReadback_eq_actual_difference
  tautologicalReadback := localWholeTautologicalInclusion_readback
  tautologicalFixed := localIntegralScalarTautologicalReadback_eq_zero
  generatedUniversalOccurrenceProjects :=
    generatedUniversalSolutionOccurrence_projects
  generatedUniversalTautologicalFixed :=
    localGeneratedUniversalTautologicalReadback_eq_zero
  universalSolutionTautologicalFixed :=
    universalSolution_tautologicalReadback_eq_zero
  cyclePrimePowerLanding := pointValue_primePower_landing
  cycleQuotientZero := pointValue_quotientZero
  cycleSuccessor := wholeCoordinatePointValue_successor
  universalCycleFixed := universalSourcePoint_wholeCoordinateValue_eq_zero
  derivedSolutionRoot := blockDerivedSolutionDiagramFace_projects
  mathlibDerivedPointInstalled := fun _coordinate _zetaZero => rfl
  derivedPointLeftReadback := pointDerivedSolutionPoint_readback
  derivedPointRightReadback := pointReversedDerivedSolutionPoint_readback
  diagonalUnitNonzero := globalDiagonalUnit_ne_zero
  diagonalWhole := globalDiagonalUnit_wholeCoordinate
  diagonalQuotient := globalDiagonalUnit_quotientCoordinate

instance : Subsingleton SettledSelfDualReadout := by
  constructor
  intro left right
  cases left
  cases right
  rfl

abbrev BaseAuthoritySource :=
  CanonicalUnitArithmeticRoot.livingRoot.toAuthoritativeRoot.source

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

/-- The settlement is active only at the exact initial occurrence from which
`seedOccurrence` was generated. -/
def settledProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence =>
    PLift (current = initialCurrent)
  InactiveAt := fun _ {current} _occurrence =>
    PLift (current ≠ initialCurrent)
  classify := by
    intro projection current occurrence
    classical
    by_cases initial : current = initialCurrent
    · exact .inl ⟨initial⟩
    · exact .inr ⟨initial⟩
  PayloadAt := fun _ {_current} _occurrence _active => SettledSelfDualReadout
  project := fun _ {_current} _occurrence _active => settledSelfDualReadout

def combinedProjectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := Sum BaseAuthoritySource.projectionLaw.Projection
    settledProjectionLaw.Projection
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl base => BaseAuthoritySource.projectionLaw.ActiveAt base occurrence
    | .inr settled => settledProjectionLaw.ActiveAt settled occurrence
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl base => BaseAuthoritySource.projectionLaw.InactiveAt base occurrence
    | .inr settled => settledProjectionLaw.InactiveAt settled occurrence
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl base => BaseAuthoritySource.projectionLaw.classify base occurrence
    | .inr settled => settledProjectionLaw.classify settled occurrence
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl base => BaseAuthoritySource.projectionLaw.PayloadAt
        base occurrence active
    | .inr settled => settledProjectionLaw.PayloadAt
        settled occurrence active
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl base => BaseAuthoritySource.projectionLaw.project
        base occurrence active
    | .inr settled => settledProjectionLaw.project
        settled occurrence active

def baseInstallation : SourceNativeProjectionLaw.InstallationAt
    BaseAuthoritySource.projectionLaw combinedProjectionLaw where
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  outcome_heq := by
    intros current occurrence projection
    rcases occurrence with ⟨support, event⟩
    change RootNativeEventAt current support at event
    cases event.support_eq
    rcases projection with material | restriction
    · cases material
      rfl
    · cases restriction <;> rfl

def settledInstallation : SourceNativeProjectionLaw.InstallationAt
    settledProjectionLaw combinedProjectionLaw where
  embed := Sum.inr
  embed_injective := Sum.inr_injective
  outcome_heq := by
    intros current occurrence projection
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classificationEq :
      settledProjectionLaw.classify projection occurrence = classification
    have combinedClassificationEq :
        combinedProjectionLaw.classify (Sum.inr projection) occurrence =
          classification := by
      exact classificationEq
    cases classification with
    | inl active =>
        rw [combinedClassificationEq]
        rfl
    | inr inactive =>
        rw [combinedClassificationEq]
        rfl

/-- Same source epoch and ledger compiler; only the projection inventory is
extended. -/
def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := BaseAuthoritySource.restructuringSource
  eventInventoryAdmission := BaseAuthoritySource.eventInventoryAdmission
  lawSurface := BaseAuthoritySource.lawSurface
  projectionLaw := combinedProjectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := CanonicalUnitArithmeticRoot.emitted
  compiler_commutes := CanonicalUnitArithmeticRoot.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? ⟨V, livingRoot, temporalVisit depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history + 1) =
            some (depth + 1)
      have priorDepth :
          ProductiveFiniteRootHistoryAt.causalDepth
              (CanonicalUnitArithmeticRoot.finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history) =
            some depth at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [priorDepth]

def process : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingRoot, temporalVisit depth⟩
  stateAt_injective := by
    intro left right equality
    have depthEquality := congrArg temporalDepth? equality
    rw [temporalVisit_depth left, temporalVisit_depth right] at depthEquality
    exact Option.some.inj depthEquality
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

def baseRuntimeAt (depth : Nat) :
    LivingRuntimeState CanonicalUnitArithmeticRoot.runtimeFacade.process :=
  CanonicalUnitArithmeticRoot.runtimeSeed.advance depth

inductive CommonFace
  | goldbachAdditiveFibre
  | selfDualZetaDeterminantFibre
  deriving DecidableEq

def commonFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => CommonFace
  componentAt := fun runtime face =>
    match face with
    | .goldbachAdditiveFibre =>
        CanonicalUnitArithmeticRoot.runtimeFacade.componentAt
          (baseRuntimeAt runtime.state) .additiveRestriction
    | .selfDualZetaDeterminantFibre => settledProjectionLaw
  installationAt := fun runtime face =>
    match face with
    | .goldbachAdditiveFibre =>
        (CanonicalUnitArithmeticRoot.runtimeFacade.installationAt
          (baseRuntimeAt runtime.state) .additiveRestriction).trans
            baseInstallation
    | .selfDualZetaDeterminantFibre => settledInstallation
  projectionAt := fun runtime face =>
    match face with
    | .goldbachAdditiveFibre =>
        CanonicalUnitArithmeticRoot.runtimeFacade.projectionAt
          (baseRuntimeAt runtime.state) .additiveRestriction
    | .selfDualZetaDeterminantFibre => PUnit.unit

def commonFacadeSeed : LivingRuntimeState commonFacade.process :=
  commonFacade.seed

theorem selfDualSeed_readout_is_settlement :
    commonFacade.readoutAt commonFacadeSeed
        .selfDualZetaDeterminantFibre =
      .inl ⟨⟨rfl⟩, settledSelfDualReadout⟩ := by
  change settledProjectionLaw.outcomeAt PUnit.unit
      commonFacadeSeed.emittedOccurrence = _
  have seedCurrent : commonFacadeSeed.current.visit.current =
      initialCurrent := rfl
  have classifier :
      settledProjectionLaw.classify PUnit.unit
          commonFacadeSeed.emittedOccurrence = .inl ⟨seedCurrent⟩ := by
    simp only [settledProjectionLaw]
    split
    · apply congrArg Sum.inl
      exact Subsingleton.elim _ _
    · rename_i notInitial
      exact False.elim (notInitial seedCurrent)
  unfold SourceNativeProjectionLaw.outcomeAt
  rw [classifier]
  apply congrArg Sum.inl
  apply Sigma.ext
  · apply PLift.down_injective
    exact Subsingleton.elim _ _
  · change HEq settledSelfDualReadout settledSelfDualReadout
    rfl

theorem coversAt_factorizes
    (runtime : LivingRuntimeState commonFacade.process)
    (face : commonFacade.FaceAt runtime) :
    commonFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (commonFacade.readoutAt runtime face)
        (runtime.tick.generated.projectionOutcome
          ((commonFacade.installationAt runtime face).embed
            (commonFacade.projectionAt runtime face))) ∧
      runtime.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor runtime.state) :=
  commonFacade.readoutAt_factorizes runtime face

theorem both_faces_share_occurrence_wholeLedger_and_one_next :
    commonFacadeSeed.tick.generated.occurrence =
        commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          commonFacadeSeed.current.visit.current ∧
      HEq commonFacadeSeed.tick.generated.wholeLedgerWriteBack
        (commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          commonFacadeSeed.current.visit.current) ∧
      commonFacadeSeed.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor commonFacadeSeed.state) := by
  have additive := coversAt_factorizes commonFacadeSeed
    .goldbachAdditiveFibre
  have selfDual := coversAt_factorizes commonFacadeSeed
    .selfDualZetaDeterminantFibre
  exact ⟨additive.2.1, selfDual.2.2.1, additive.2.2.2.2⟩

end
end CanonicalUnitArithmeticIntegralFixedNamedFacade
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
