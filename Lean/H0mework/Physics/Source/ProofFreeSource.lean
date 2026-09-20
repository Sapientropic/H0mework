import H0mework.Physics.Admission.SU7MotherPhysicalUnifiedAdmissionCredential
import H0mework.Arithmetic.SourceAdmission.A6P506ObservablePhysicalAdmissionCore

/-!
# One proof-free Stage-8 source for physical and P506/L0 projections

The former Stage-8 root accepted an arbitrary lineage type, an external
lineage equality, and a separately hard-coded endpoint `11`.  This module
replaces that mouth with raw source coordinates only.  One full six-node L0
phase potential generates both the physical phase amplitude and the exact
observable P506/L0 cochain.  The A6 root/moves generate the current label;
the selected endpoint is then read from that generated label by the existing
left-anchor grammar.

No endpoint, lineage equality, Factor atomhood, representation certificate,
breaking scalar, mass matrix, matter state, or current is a source field.
-/

namespace SaturationMonoid.PhysicsCore.StageEightProofFreeSource

open ProofFreeRicherAnholonomicSource
open SU7RicherLineageResponsibility
open SU7A6GaugeStableRootGraphAdapter
open PhysicalUnifiedAdmission
open PhysicalIIPlusFrechetVariation
open SourceGeneratedPhysicalPlebanskiConfiguration
open NonseparablePhysicalUnifiedAdmission
open SU7MotherPhysicalUnifiedAdmission
open NonseparableGravityGaugeSourceAction
open NonzeroSourceGaugeStationaryConfiguration
open EmpiricalReferenceScaleCouplingBoundary
open RepresentationArithmeticAtomProjectionDefect
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open A6CrystalObservedSourceTrace
open StandardModelConstraint

noncomputable section

/-- Raw Stage-8 source coordinates.  The P506 phase input is a potential, not
an exact-lineage receipt; its observable cochain is generated below. -/
structure Source where
  sourceRoot : SU7A6WeightLabel
  sourceMoves : SourcePathData
  p506PhasePotential : P506SourceAffineL0PhaseNode → Int
  sigmaSeed : Nat
  colorScale : Nat
  coframeLinearCoefficient : LorentzianCoframeDerivative

namespace Source

/-- The physical finite-ring amplitude is the distinguished edge displacement
of the same full L0 potential. -/
def physicalPhaseAmplitude (source : Source) : Int :=
  source.p506PhasePotential (Sum.inl .t1) -
    source.p506PhasePotential (Sum.inl .t0)

/-- Dependency-light physical projection consumed by Stages 4--6. -/
def toPhysicalSource (source : Source) :
    ProofFreeRicherAnholonomicSource.Source where
  sourceRoot := source.sourceRoot
  sourceMoves := source.sourceMoves
  phaseAmplitude := source.physicalPhaseAmplitude
  sigmaSeed := source.sigmaSeed
  colorScale := source.colorScale
  coframeLinearCoefficient := source.coframeLinearCoefficient

/-- Gauge-invariant cochain generated from the raw L0 potential. -/
def p506PhaseCochain (source : Source) :
    P506SourceAffineL0PhaseNode → P506SourceAffineL0PhaseNode → Int :=
  fun initial terminal =>
    source.p506PhasePotential terminal - source.p506PhasePotential initial

/-- Actual observable P506/L0 lineage generated fieldwise from this source.
Branch and incidence are the existing A6 grammar readouts; endpoint selection
is deliberately absent. -/
def generatedP506L0Lineage (source : Source) :
    P506SourceAffineL0ObservableLineageReference where
  rootLabel := source.sourceRoot
  rootMoves := source.sourceMoves.map toA6Root
  producerDepth := source.sourceMoves.card
  rootMoves_card := by simp
  sourceLabel := generatedLabel source.sourceRoot source.sourceMoves
  branch := .e
  incidence := .colorWeak
  phaseCochain := source.p506PhaseCochain
  sigmaTag := source.toPhysicalSource.sigma

/-- Endpoint is a downstream grammar readout of the generated lineage. -/
def generatedSelectedEndpoint
    (source : Source)
    (height_pos :
      0 < su7A6SignedHeight source.generatedP506L0Lineage.sourceLabel) : Nat :=
  source.generatedP506L0Lineage.selectedEndpoint height_pos

end Source

/-- Canonical positive Stage-8 source.  It stores the actual `(5,7)` root and
the depth-zero L0 potential, not their equality to a reference or endpoint. -/
def canonicalSource : Source where
  sourceRoot := su7A6FiveSevenSourceLabel
  sourceMoves := 0
  p506PhasePotential := n10FiveSevenPhasePotential 0
  sigmaSeed := 0
  colorScale := 1
  coframeLinearCoefficient := shearCoefficient

@[simp] theorem canonicalSource_physicalPhaseAmplitude :
    canonicalSource.physicalPhaseAmplitude = 1 := by
  norm_num [canonicalSource, Source.physicalPhaseAmplitude,
    n10FiveSevenPhasePotential]

/-- First corrected producer nail: the full canonical P506/L0 observable
lineage is computed from the proof-free Stage-8 source. -/
theorem canonicalSource_generates_exactP506L0Lineage :
    canonicalSource.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference := by
  apply P506SourceAffineL0ObservableLineageReference.ext
  · rfl
  · simp [Source.generatedP506L0Lineage, canonicalSource]
  · simp [Source.generatedP506L0Lineage, canonicalSource,
      canonicalP506SourceAffineL0ObservableLineageReference_sourceLabel]
  · rfl
  · rfl
  · rfl
  · funext initial terminal
    rfl
  · norm_num [Source.generatedP506L0Lineage, Source.toPhysicalSource,
      ProofFreeRicherAnholonomicSource.Source.sigma, canonicalSource,
      canonicalP506SourceAffineL0ObservableLineageReference,
      p506SourceAffineL0ObservableLineageReferenceOfTrace,
      canonicalP506SourceAffineL0LineageReference,
      n10FiveSevenObservedTrace]

theorem canonicalSource_generatedLineage_height_pos :
    0 < su7A6SignedHeight
      canonicalSource.generatedP506L0Lineage.sourceLabel := by
  rw [canonicalSource_generates_exactP506L0Lineage]
  exact canonicalP506SourceAffineL0ObservableLineageReference_height_pos

/-- Endpoint `11` is generated by the existing grammar from the generated
lineage; it is not a source field or a constructor literal. -/
@[simp] theorem canonicalSource_generates_selectedEndpoint_eleven :
    canonicalSource.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11 := by
  unfold Source.generatedSelectedEndpoint
  simpa only [canonicalSource_generates_exactP506L0Lineage] using
    canonicalP506SourceAffineL0ObservableLineageReference_selectedEndpoint

/-- Endpoint-only equality remains insufficient: the existing zero-phase
lookalike has endpoint `11` but cannot equal this source-generated lineage. -/
theorem endpointEleven_zeroPhaseLookalike_rejected :
    p506EndpointElevenZeroPhaseLineageLookalike ≠
      canonicalSource.generatedP506L0Lineage := by
  rw [canonicalSource_generates_exactP506L0Lineage]
  exact p506EndpointElevenZeroPhaseLineageLookalike_ne_canonical

/-! ## Stage-6 physical projection of the same source -/

abbrev canonicalPhysicalSource : ProofFreeRicherAnholonomicSource.Source :=
  canonicalSource.toPhysicalSource

theorem canonicalPhysicalSource_coframeAt_eq_transvection (point : BasePoint) :
    canonicalPhysicalSource.coframeAt point =
      Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
        (point 2) := by
  ext internal coordinate
  fin_cases internal <;> fin_cases coordinate <;>
    simp [canonicalPhysicalSource, canonicalSource, Source.toPhysicalSource,
      ProofFreeRicherAnholonomicSource.Source.coframeAt, shearCoefficient,
      Matrix.transvection, Matrix.single]

theorem canonicalPhysicalSource_coframeAt_det (point : BasePoint) :
    Matrix.det (canonicalPhysicalSource.coframeAt point) = 1 := by
  rw [canonicalPhysicalSource_coframeAt_eq_transvection]
  exact Matrix.det_transvection_of_ne 0 1 (by norm_num) (point 2)

theorem canonicalPhysicalSource_globally_nondegenerate (point : BasePoint) :
    Matrix.det (canonicalPhysicalSource.coframeAt point) ≠ 0 := by
  rw [canonicalPhysicalSource_coframeAt_det]
  norm_num

theorem canonicalPhysicalSource_field_nonzero :
    canonicalPhysicalSource.field ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero 0) 0
  norm_num [canonicalPhysicalSource, canonicalSource, Source.toPhysicalSource,
    ProofFreeRicherAnholonomicSource.Source.field,
    rawCodeColorLoopMatrix] at hentry

theorem canonicalPhysicalSource_anholonomic :
    canonicalPhysicalSource.IsAnholonomic := by
  refine ⟨0, 2, 1, ?_⟩
  simp [canonicalPhysicalSource, canonicalSource, Source.toPhysicalSource,
    ProofFreeRicherAnholonomicSource.Source.anholonomy, shearCoefficient]

theorem canonicalPhysicalSource_physicalIIPlus_nonzero :
    physicalIIPlusBivector (canonicalPhysicalSource.jetAt 0).coframe ≠ 0 := by
  simpa using physicalIIPlusBivector_not_zero

def canonicalPhysicalStageFour :
    PhysicalDynamicsAdmissionCredential canonicalPhysicalSource unitBoundary :=
  physicalDynamicsAdmissionCredentialOf canonicalPhysicalSource unitBoundary
    (by simp [canonicalPhysicalSource, Source.toPhysicalSource])
    canonicalPhysicalSource_field_nonzero
    canonicalPhysicalSource_anholonomic
    canonicalPhysicalSource_physicalIIPlus_nonzero

theorem canonicalPhysicalSource_curvature_component :
    canonicalPhysicalSource.coordinateCurvatureAtOrigin 0 1 0 1 =
      -(1 / 4 : ℝ) := by
  simp [ProofFreeRicherAnholonomicSource.Source.coordinateCurvatureAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.raisedChristoffelDerivativeAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.inverseMetricDerivativeAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.metricFirstDerivativeAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.loweredChristoffelDerivativeAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.metricSecondDerivativeAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.raisedChristoffelAtOrigin,
    ProofFreeRicherAnholonomicSource.Source.loweredChristoffelAtOrigin,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    canonicalPhysicalSource, canonicalSource, Source.toPhysicalSource,
    Source.physicalPhaseAmplitude, n10FiveSevenPhasePotential,
    shearCoefficient, minkowskiInternalSign, Fin.sum_univ_four]
  all_goals norm_num

theorem canonicalPhysicalSource_gaugeCurvature_component :
    sourceGaugeCurvature canonicalPhysicalSource 0 = (1 / 4 : ℝ) := by
  change sourceCurvatureVector canonicalPhysicalSource (0, 0) = (1 / 4 : ℝ)
  norm_num [sourceCurvatureVector, vectorOfPhysicalBivector,
    ProofFreeRicherAnholonomicSource.Source.lorentzCurvatureAtOrigin,
    pairFirst, pairSecond, minkowskiInternalSign,
    canonicalPhysicalSource_curvature_component]

theorem canonicalPhysicalSource_gaugeCurvature_nonzero :
    sourceGaugeCurvature canonicalPhysicalSource ≠ 0 := by
  intro hzero
  have hcomponent := congrArg
    (fun curvature : DynamicGaugeVector => curvature 0) hzero
  rw [canonicalPhysicalSource_gaugeCurvature_component] at hcomponent
  norm_num at hcomponent

def canonicalPhysicalStageFive :
    NonseparablePhysicalUnifiedAdmissionCredential
      canonicalPhysicalSource unitBoundary :=
  nonseparablePhysicalCredentialOf canonicalPhysicalSource unitBoundary
    canonicalPhysicalStageFour canonicalPhysicalSource_gaugeCurvature_nonzero

/-- The same proof-free Stage-8 source therefore also generates the existing
dependency-light Stage-6 mother credential. -/
def canonicalPhysicalStageSix :
    SU7MotherPhysicalUnifiedAdmissionCredential
      canonicalPhysicalSource unitBoundary :=
  su7MotherPhysicalCredentialOf canonicalPhysicalSource unitBoundary
    canonicalPhysicalStageFive

theorem canonicalSource_generates_lineage_endpoint_and_stageSix :
    canonicalSource.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      canonicalSource.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      Nonempty
        (SU7MotherPhysicalUnifiedAdmissionCredential
          canonicalPhysicalSource unitBoundary) :=
  ⟨canonicalSource_generates_exactP506L0Lineage,
    canonicalSource_generates_selectedEndpoint_eleven,
    ⟨canonicalPhysicalStageSix⟩⟩

end

end SaturationMonoid.PhysicsCore.StageEightProofFreeSource
