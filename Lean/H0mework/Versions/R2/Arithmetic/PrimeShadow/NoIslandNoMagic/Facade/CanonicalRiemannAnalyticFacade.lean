import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticIntegralFixedNamedFacade
import H0mework.Versions.R2.Arithmetic.RiemannSource.ThetaEulerOverlap
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.DerivedPointReadback
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.Disposition
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.QRichSeparator
import H0mework.Versions.R2.Arithmetic.RiemannLineage.LineagePoint
import H0mework.Versions.R2.Arithmetic.MellinBoundary.ProperMellinScalarEnvelopeOccurrence
import H0mework.Versions.R2.Arithmetic.MellinBoundary.ProperMellinLowHighRelativeOccurrence
import H0mework.Versions.R2.Arithmetic.MuntzAction.LocalEndpointDifferentialResidual
import H0mework.Versions.R2.Arithmetic.RiemannLineage.ClozelProperMellinScalarRelationIncidence
import H0mework.Versions.R2.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Face.ClozelBurnolPhysicalActionProjectionLaw
import H0mework.Versions.R2.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Claim.ClozelBurnolSpectralActualityClaimProjectionLaw

/-!
# Named facade for the source-generated Riemann analytic face

This extends the existing canonical arithmetic facade by three projection
inventory entries.  The source, event algebra, emitter, ledger compiler, law
epoch, and successor are unchanged.  The payloads are the theta–Mellin
continuation, its certified theta--Burnol common-action physical face, and
the dependent zero-field spectral-actuality claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemannAnalyticFacade

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticRoot
open CanonicalRiemann
open CanonicalRiemann.InverseZeroFibre
open CanonicalRiemann.QRich
open BurnolPhysicalActionProjection
open CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.SpectralActuality
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CategoryTheory
open Complex MeasureTheory Set

noncomputable section

namespace PriorFacade

abbrev AuthoritySource :=
  CanonicalUnitArithmeticIntegralFixedNamedFacade.authoritySource

abbrev LedgerSource :=
  AuthoritySource.restructuringSource.toLedgerSource

end PriorFacade

/-- Low-universe named readout of the full generated analytic chain.  It
stores only machine propositions; the high-universe source objects remain in
their owning occurrences and cannot be copied into the facade payload. -/
structure SourceGeneratedRiemannAnalyticReadout : Type where
  private mk ::
  finiteThetaProjects : ∀ stage,
    (finiteThetaOccurrence stage).map Sigma.fst = globalGermOccurrence
  zeroModeProjects :
    thetaZeroModeOccurrence.map Sigma.fst = globalGermOccurrence
  weakPairProjects :
    generatedRiemannWeakFEPairOccurrence.map Sigma.fst = globalGermOccurrence
  analyticContinuationProjects :
    generatedRiemannAnalyticContinuationOccurrence.map Sigma.fst =
      globalGermOccurrence
  correctedMellinEntire :
    Differentiable ℂ
      (generatedCompletedRiemannZeta₀ globalGermOccurrence.root)
  completedFunctionalEquation : ∀ s,
    generatedCompletedRiemannZeta globalGermOccurrence.root (1 - s) =
      generatedCompletedRiemannZeta globalGermOccurrence.root s
  generatedMellin : ∀ {s : ℂ}, 1 < s.re →
    HasMellin
      ((GeneratedRiemannWeakFEPairAt.generate
          globalGermOccurrence.root).pair.f · -
        (GeneratedRiemannWeakFEPairAt.generate
          globalGermOccurrence.root).pair.f₀)
      (s / 2)
      ((GeneratedRiemannWeakFEPairAt.generate
          globalGermOccurrence.root).pair.Λ (s / 2))
  analyticAwayOne :
    AnalyticOnNhd ℂ
      (generatedRiemannZeta globalGermOccurrence.root) ({1} : Set ℂ)ᶜ
  eulerOverlap : ∀ {s : ℂ}, 1 < s.re →
    generatedRiemannZeta globalGermOccurrence.root s =
      globalDeterminantCoordinateGerm s
  zeroReadProjects : ∀ observation,
    (zeroObservationReadoutOccurrence observation).map Sigma.fst =
      generatedRiemannAnalyticContinuationOccurrence
  properMellinEnvelopeProjects : ∀ observation,
    (ProperMellinScalarEnvelopeOccurrence.occurrence observation).map Prod.fst =
      zeroObservationReadoutOccurrence observation
  properMellinEnvelopeTotal :
    Nonempty
      (SourceGeneratedScalarExactEnvelope.UniversalPerfectEnvelope
        ProperMellinScalarEnvelope.evaluation)
  properMellinFullRowProjects : ∀ observation stage,
    (zeroOwnedProperMellinPointFullRowIncidenceOccurrence
        observation stage).map Sigma.fst =
      zeroObservationReadoutOccurrence observation
  properMellinPresentedCycle : ∀ observation stage value,
    (ProperMellinScalarRelationIncidence.relationFace
      observation stage).differentialPresentedMap 1 2
        (ProperMellinScalarRelationIncidence.presentedDegreeOneMap
          observation stage value) = 0
  properMellinStarInversionInvolutive : ∀ value : PositiveMellinL1,
    positiveMellinL1StarInversion
        (positiveMellinL1StarInversion value) = value
  properMellinLowHighResidual : ∀ {owner : GlobalGermOwner}
      (observation : GeneratedRiemannZeroObservationAt owner)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)),
    positiveMellinL1StageZeroStarInversionResidual
        observation nontrivial ≠ 0 ∧
      (∫ t : ℝ in stageZeroLowWindow,
          (positiveMellinL1StageZeroStarInversionResidual
            observation nontrivial : ℝ → ℂ) t) =
        -(blockQRichSuccessorScale 0 : ℂ) ^
          (-(coordinateReversal observation.coordinate / 2))
  properMellinLowHighProjects : ∀
      (observation : GeneratedRiemannZeroObservation)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)),
    (zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial).map Sigma.fst =
      zeroObservationReadoutOccurrence observation
  properMellinLowHighFold : ∀
      (observation : GeneratedRiemannZeroObservation)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)),
    properMellinLowHighResidualTraceReadout
        (zeroOwnedProperMellinLowHighRelativeOccurrence
          observation nontrivial) =
      (zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial).fold
        (RootedAccountedUnfolding.additiveFoldAlgebra
          properMellinLowHighResidualWeight)
  localEndpointResidualProjects : ∀
      (observation : GeneratedRiemannZeroObservation)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) stage,
    (LocalEndpointDifferentialResidual.occurrence
        observation nontrivial stage).map Sigma.fst =
      zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial
  localEndpointResidualZeroIffFixed : ∀
      (observation : GeneratedRiemannZeroObservation)
      (nontrivial :
        ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) stage
      (_row : FactorRow seedOccurrence.root stage),
    (LocalEndpointDifferentialResidual.occurrence
        observation nontrivial stage).root.2 = 0 ↔
      observation.coordinate = coordinateReversal observation.coordinate
  completeInverseFibre : ∀ observation,
    Nonempty (InverseZeroFibre observation ≃ Sum ℂ ℂ)
  nontrivialPresentationResidual : ∀ observation,
    ¬∃ center : InverseZeroFibre observation,
      ∀ candidate,
        ReversalPresentationEquivalent observation candidate center
  selectedDerivedReadback : ∀ observation
      (fibre : InverseZeroFibre observation) stage
      (row : FactorRow seedOccurrence.root stage),
    InverseZeroFibre.selectedDerivedReadback fibre stage row =
      observation.coordinate
  partnerDerivedReadback : ∀ observation
      (fibre : InverseZeroFibre observation) stage
      (row : FactorRow seedOccurrence.root stage),
    InverseZeroFibre.partnerDerivedReadback fibre stage row =
      InverseZeroFibre.partnerResidual fibre
  qRichStrictCycle : ∀ stage base,
    blockFactorizationDifferential seedOccurrence.root stage
        (blockQRichEndpointVertexMap stage base) = 0
  qRichQuotientZero : ∀ stage
      (row : FactorRow seedOccurrence.root stage) base,
    PrimePowerQuotientEvaluation.evaluator
        (BlockInner seedOccurrence.root stage)
        (blockWholeAntiInvariantProjection stage
          (blockQRichEndpointVertexMap stage base))
        (rowPrime row) (rowExponent row) = 0
  qRichLineageNatural : ∀ stage,
    qRichLineagePoint (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage =
      qRichLineageRestriction stage ≫ qRichLineagePoint stage
  qRichDerivedLineageNatural : ∀ stage,
    qRichDerivedLineagePoint (stage + 1) ≫
        CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom.localCorrectedEndpointRestriction
          stage =
      qRichLineageSingleOneRestriction stage ≫
        qRichDerivedLineagePoint stage
  fullRowTotalNatural : ∀ stage,
    (fullRowDerivedCube stage).horizontalTotalTransition ≫
        (fullRowDerivedSquare stage).generatedTotalIso.hom =
      (fullRowDerivedSquare (stage + 1)).generatedTotalIso.hom ≫
        (fullRowDerivedCube stage).verticalTotalTransition
  fibreSeparatorFormula : ∀ observation
      (fibre : InverseZeroFibre observation) stage
      (row : FactorRow seedOccurrence.root stage),
    InverseZeroFibre.branchNormalizedQRichSeparator fibre stage row =
      -(quotientCoefficient row : ℂ) *
        (observation.coordinate - InverseZeroFibre.partnerResidual fibre)
  fibreSeparatorZeroIff : ∀ observation
      (fibre : InverseZeroFibre observation) stage
      (row : FactorRow seedOccurrence.root stage),
    InverseZeroFibre.branchNormalizedQRichSeparator fibre stage row = 0 ↔
      InverseZeroFibre.partnerResidual fibre = observation.coordinate

def sourceGeneratedRiemannAnalyticReadout :
    SourceGeneratedRiemannAnalyticReadout where
  finiteThetaProjects := finiteThetaOccurrence_projects
  zeroModeProjects := thetaZeroModeOccurrence_projects
  weakPairProjects := generatedRiemannWeakFEPairOccurrence_projects
  analyticContinuationProjects :=
    generatedRiemannAnalyticContinuationOccurrence_projects
  correctedMellinEntire :=
    differentiable_generatedCompletedRiemannZeta₀ _
  completedFunctionalEquation :=
    generatedCompletedRiemannZeta_one_sub _
  generatedMellin := generatedTheta_hasMellin _
  analyticAwayOne := analyticOn_generatedRiemannZeta_awayOne _
  eulerOverlap :=
    generatedRiemannZeta_eq_globalDeterminantCoordinateGerm _
  zeroReadProjects := zeroObservationReadoutOccurrence_projects
  properMellinEnvelopeProjects :=
    ProperMellinScalarEnvelopeOccurrence.occurrence_projects
  properMellinEnvelopeTotal := ProperMellinScalarEnvelope.exactEnvelope_total
  properMellinFullRowProjects :=
    zeroOwnedProperMellinPointFullRowIncidenceOccurrence_projects
  properMellinPresentedCycle :=
    ProperMellinScalarRelationIncidence.presentedDegreeOneMap_differential_zero
  properMellinStarInversionInvolutive :=
    positiveMellinL1StarInversion_involutive
  properMellinLowHighResidual := fun observation nontrivial =>
    ⟨positiveMellinL1StageZeroStarInversionResidual_ne_zero
        observation nontrivial,
      positiveMellinL1StageZeroStarInversionResidual_coordinate
        observation nontrivial⟩
  properMellinLowHighProjects :=
    zeroOwnedProperMellinLowHighRelativeOccurrence_projects
  properMellinLowHighFold :=
    zeroOwnedProperMellinLowHighRelativeOccurrence_fold_unique_consumer
  localEndpointResidualProjects :=
    LocalEndpointDifferentialResidual.occurrence_projects
  localEndpointResidualZeroIffFixed :=
    LocalEndpointDifferentialResidual.occurrence_root_zero_iff_fixed
  completeInverseFibre := fun observation =>
    ⟨InverseZeroFibre.completeEquiv observation⟩
  nontrivialPresentationResidual :=
    InverseZeroFibre.no_single_reversal_presentation_class
  selectedDerivedReadback := fun _observation fibre stage row =>
    InverseZeroFibre.selectedDerivedReadback_eq_observation
      fibre stage row
  partnerDerivedReadback := fun _observation fibre stage row =>
    InverseZeroFibre.partnerDerivedReadback_eq_residual fibre stage row
  qRichStrictCycle :=
    blockQRichEndpointVertexMap_differential_zero
  qRichQuotientZero := blockQRichEndpoint_quotientZero
  qRichLineageNatural := qRichLineagePoint_successor
  qRichDerivedLineageNatural := qRichDerivedLineagePoint_successor
  fullRowTotalNatural := fullRowGeneratedTotalIso_naturality
  fibreSeparatorFormula := fun _observation fibre stage row =>
    InverseZeroFibre.branchNormalizedQRichSeparator_eq fibre stage row
  fibreSeparatorZeroIff := fun _observation fibre stage row =>
    InverseZeroFibre.branchNormalizedQRichSeparator_eq_zero_iff
      fibre stage row

instance : Subsingleton SourceGeneratedRiemannAnalyticReadout := by
  constructor
  intro left right
  cases left
  cases right
  rfl

/-- The analytic face is active at the exact initial occurrence that owns the
canonical determinant germ. -/
def analyticProjectionLaw :
    SourceNativeProjectionLaw PriorFacade.LedgerSource where
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
  PayloadAt := fun _ {_current} _occurrence _active =>
    SourceGeneratedRiemannAnalyticReadout
  project := fun _ {_current} _occurrence _active =>
    sourceGeneratedRiemannAnalyticReadout

def combinedProjectionLaw :
    SourceNativeProjectionLaw PriorFacade.LedgerSource where
  Projection := Sum PriorFacade.AuthoritySource.projectionLaw.Projection
    (Sum analyticProjectionLaw.Projection
      (Sum projectionLaw.Projection spectralActualityProjectionLaw.Projection))
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl prior =>
        PriorFacade.AuthoritySource.projectionLaw.ActiveAt prior occurrence
    | .inr (.inl analytic) =>
        analyticProjectionLaw.ActiveAt analytic occurrence
    | .inr (.inr (.inl physical)) =>
        projectionLaw.ActiveAt physical occurrence
    | .inr (.inr (.inr actuality)) =>
        spectralActualityProjectionLaw.ActiveAt actuality occurrence
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl prior =>
        PriorFacade.AuthoritySource.projectionLaw.InactiveAt prior occurrence
    | .inr (.inl analytic) =>
        analyticProjectionLaw.InactiveAt analytic occurrence
    | .inr (.inr (.inl physical)) =>
        projectionLaw.InactiveAt physical occurrence
    | .inr (.inr (.inr actuality)) =>
        spectralActualityProjectionLaw.InactiveAt actuality occurrence
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl prior =>
        PriorFacade.AuthoritySource.projectionLaw.classify prior occurrence
    | .inr (.inl analytic) => analyticProjectionLaw.classify analytic occurrence
    | .inr (.inr (.inl physical)) =>
        projectionLaw.classify physical occurrence
    | .inr (.inr (.inr actuality)) =>
        spectralActualityProjectionLaw.classify actuality occurrence
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl prior =>
        PriorFacade.AuthoritySource.projectionLaw.PayloadAt
          prior occurrence active
    | .inr (.inl analytic) =>
        analyticProjectionLaw.PayloadAt analytic occurrence active
    | .inr (.inr (.inl physical)) =>
        projectionLaw.PayloadAt physical occurrence active
    | .inr (.inr (.inr actuality)) =>
        spectralActualityProjectionLaw.PayloadAt actuality occurrence active
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl prior =>
        PriorFacade.AuthoritySource.projectionLaw.project
          prior occurrence active
    | .inr (.inl analytic) =>
        analyticProjectionLaw.project analytic occurrence active
    | .inr (.inr (.inl physical)) =>
        projectionLaw.project physical occurrence active
    | .inr (.inr (.inr actuality)) =>
        spectralActualityProjectionLaw.project actuality occurrence active

def priorInstallation : SourceNativeProjectionLaw.InstallationAt
    PriorFacade.AuthoritySource.projectionLaw combinedProjectionLaw where
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  outcome_heq := by
    intros current occurrence projection
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classificationEq :
      PriorFacade.AuthoritySource.projectionLaw.classify projection occurrence =
        classification
    have combinedClassificationEq :
        combinedProjectionLaw.classify (Sum.inl projection) occurrence =
          classification := by
      exact classificationEq
    cases classification with
    | inl active =>
        rw [combinedClassificationEq]
        rfl
    | inr inactive =>
        rw [combinedClassificationEq]
        rfl

def analyticInstallation : SourceNativeProjectionLaw.InstallationAt
    analyticProjectionLaw combinedProjectionLaw where
  embed := fun projection => Sum.inr (Sum.inl projection)
  embed_injective := by
    intro left right equality
    exact Sum.inl.inj (Sum.inr.inj equality)
  outcome_heq := by
    intros current occurrence projection
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classificationEq :
      analyticProjectionLaw.classify projection occurrence = classification
    have combinedClassificationEq :
        combinedProjectionLaw.classify (Sum.inr (Sum.inl projection)) occurrence =
          classification := by
      exact classificationEq
    cases classification with
    | inl active =>
        rw [combinedClassificationEq]
        rfl
    | inr inactive =>
        rw [combinedClassificationEq]
        rfl

def physicalInstallation : SourceNativeProjectionLaw.InstallationAt
    projectionLaw combinedProjectionLaw where
  embed := fun projection => Sum.inr (Sum.inr (Sum.inl projection))
  embed_injective := by
    intro left right equality
    exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj equality))
  outcome_heq := by
    intros current occurrence projection
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classificationEq :
      projectionLaw.classify projection occurrence = classification
    have combinedClassificationEq :
        combinedProjectionLaw.classify
          (Sum.inr (Sum.inr (Sum.inl projection))) occurrence =
            classification := by
      exact classificationEq
    cases classification with
    | inl active =>
        rw [combinedClassificationEq]
        rfl
    | inr inactive =>
        rw [combinedClassificationEq]
        rfl

def spectralActualityInstallation : SourceNativeProjectionLaw.InstallationAt
    spectralActualityProjectionLaw combinedProjectionLaw where
  embed := fun projection => Sum.inr (Sum.inr (Sum.inr projection))
  embed_injective := by
    intro left right equality
    exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj equality))
  outcome_heq := by
    intros current occurrence projection
    unfold SourceNativeProjectionLaw.outcomeAt
    generalize classificationEq :
      spectralActualityProjectionLaw.classify projection occurrence =
        classification
    have combinedClassificationEq :
        combinedProjectionLaw.classify
          (Sum.inr (Sum.inr (Sum.inr projection))) occurrence =
            classification := by
      exact classificationEq
    cases classification with
    | inl active =>
        rw [combinedClassificationEq]
        rfl
    | inr inactive =>
        rw [combinedClassificationEq]
        rfl

/-- Same root authority with three additional projection inventory entries. -/
def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := PriorFacade.AuthoritySource.restructuringSource
  eventInventoryAdmission := PriorFacade.AuthoritySource.eventInventoryAdmission
  lawSurface := PriorFacade.AuthoritySource.lawSurface
  projectionLaw := combinedProjectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := CanonicalUnitArithmeticRoot.emitted
  compiler_commutes :=
    CanonicalUnitArithmeticRoot.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
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

def priorRuntimeAt (depth : Nat) : LivingRuntimeState
    CanonicalUnitArithmeticIntegralFixedNamedFacade.commonFacade.process :=
  CanonicalUnitArithmeticIntegralFixedNamedFacade.commonFacadeSeed.advance depth

inductive CommonFace
  | prior
      (face : CanonicalUnitArithmeticIntegralFixedNamedFacade.CommonFace)
  | sourceGeneratedThetaMellin
  | burnolPhysicalAction
  | spectralActuality (projection : ProjectionAt)
  deriving DecidableEq

def commonFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => CommonFace
  componentAt := fun runtime face =>
    match face with
    | .prior prior =>
        CanonicalUnitArithmeticIntegralFixedNamedFacade.commonFacade.componentAt
          (priorRuntimeAt runtime.state) prior
    | .sourceGeneratedThetaMellin => analyticProjectionLaw
    | .burnolPhysicalAction => projectionLaw
    | .spectralActuality _projection => spectralActualityProjectionLaw
  installationAt := fun runtime face =>
    match face with
    | .prior prior =>
        (CanonicalUnitArithmeticIntegralFixedNamedFacade.commonFacade.installationAt
          (priorRuntimeAt runtime.state) prior).trans priorInstallation
    | .sourceGeneratedThetaMellin => analyticInstallation
    | .burnolPhysicalAction => physicalInstallation
    | .spectralActuality _projection => spectralActualityInstallation
  projectionAt := fun runtime face =>
    match face with
    | .prior prior =>
        CanonicalUnitArithmeticIntegralFixedNamedFacade.commonFacade.projectionAt
          (priorRuntimeAt runtime.state) prior
    | .sourceGeneratedThetaMellin => PUnit.unit
    | .burnolPhysicalAction => PUnit.unit
    | .spectralActuality projection => projection

def commonFacadeSeed : LivingRuntimeState commonFacade.process :=
  commonFacade.seed

theorem analyticSeed_readout_is_generated :
    commonFacade.readoutAt commonFacadeSeed .sourceGeneratedThetaMellin =
      .inl ⟨⟨rfl⟩,
        sourceGeneratedRiemannAnalyticReadout⟩ := by
  change analyticProjectionLaw.outcomeAt PUnit.unit
      commonFacadeSeed.emittedOccurrence = _
  have seedCurrent : commonFacadeSeed.current.visit.current =
      initialCurrent := rfl
  have classifier :
      analyticProjectionLaw.classify PUnit.unit
          commonFacadeSeed.emittedOccurrence = .inl ⟨seedCurrent⟩ := by
    simp only [analyticProjectionLaw]
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
  · rfl

theorem burnolPhysicalActionSeed_readout_is_generated :
    commonFacade.readoutAt commonFacadeSeed .burnolPhysicalAction =
      .inl ⟨⟨rfl⟩,
        sourceGeneratedBurnolPhysicalActionReadout⟩ := by
  change projectionLaw.outcomeAt PUnit.unit
      commonFacadeSeed.emittedOccurrence = _
  have seedCurrent : commonFacadeSeed.current.visit.current =
      initialCurrent := rfl
  have classifier :
      projectionLaw.classify PUnit.unit commonFacadeSeed.emittedOccurrence =
        .inl ⟨seedCurrent⟩ := by
    simp only [projectionLaw]
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
  · rfl

theorem spectralActualitySeed_readout_is_generated
    (projection : ProjectionAt) :
    commonFacade.readoutAt commonFacadeSeed (.spectralActuality projection) =
      .inl ⟨⟨rfl⟩,
        projectionPackage projection⟩ := by
  change spectralActualityProjectionLaw.outcomeAt projection
      commonFacadeSeed.emittedOccurrence = _
  have seedCurrent : commonFacadeSeed.current.visit.current =
      initialCurrent := rfl
  have classifier :
      spectralActualityProjectionLaw.classify projection
          commonFacadeSeed.emittedOccurrence = .inl ⟨seedCurrent⟩ := by
    change spectralActualityPendingClaimProjectionLaw.classify projection
      commonFacadeSeed.emittedOccurrence = .inl ⟨seedCurrent⟩
    simp only [spectralActualityPendingClaimProjectionLaw]
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
  · rfl

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

/-- The old self-dual row and the new analytic row consume the same update,
whole ledger, and unique generated next. -/
theorem analytic_and_selfDual_share_occurrence_wholeLedger_and_one_next :
    commonFacadeSeed.tick.generated.occurrence =
        commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          commonFacadeSeed.current.visit.current ∧
      HEq commonFacadeSeed.tick.generated.wholeLedgerWriteBack
        (commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          commonFacadeSeed.current.visit.current) ∧
      commonFacadeSeed.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor commonFacadeSeed.state) := by
  have analytic := coversAt_factorizes commonFacadeSeed
    .sourceGeneratedThetaMellin
  have selfDual := coversAt_factorizes commonFacadeSeed
    (.prior .selfDualZetaDeterminantFibre)
  exact ⟨analytic.2.1, selfDual.2.2.1, analytic.2.2.2.2⟩

theorem analytic_and_burnolPhysicalAction_share_occurrence_wholeLedger_and_one_next :
    commonFacadeSeed.tick.generated.occurrence =
        commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          commonFacadeSeed.current.visit.current ∧
      HEq commonFacadeSeed.tick.generated.wholeLedgerWriteBack
        (commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          commonFacadeSeed.current.visit.current) ∧
      commonFacadeSeed.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor commonFacadeSeed.state) := by
  have analytic := coversAt_factorizes commonFacadeSeed
    .sourceGeneratedThetaMellin
  have physical := coversAt_factorizes commonFacadeSeed
    .burnolPhysicalAction
  exact ⟨analytic.2.1, physical.2.2.1, analytic.2.2.2.2⟩

end
end CanonicalRiemannAnalyticFacade
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
