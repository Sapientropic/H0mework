import H0mework.Physics.Geometry.AssociatedBundles
import H0mework.Physics.Gauge.SU7MotherSourceConfiguration
import H0mework.Physics.Dirac.DiracExteriorMatterLocalGaugeLink

/-!
# Stage-9A smooth mother connection with exact Stage-8 first jet

The earlier S9-0 hypercharge bridge proves that the continuous contact trace
can generate smooth geometry and nontrivial path holonomy.  The final Stage-9
connection must additionally be the same connection already generated at
Stage 8.  This module constructs the required smooth affine extension of the
actual Stage-8 mother connection.

The Stage-8 potential is the value at the origin.  Its stored antisymmetric
first jet is extended linearly over the four-dimensional base.  Consequently
the full non-Abelian curvature at the origin is definitionally the Stage-8
mother curvature.  The source-generated affine first jet `1 + A` is exactly
the link consumed by Stage 8.  A general noncommuting matrix-transport ODE and
its analytic derivative remain outside this checkpoint.
-/

namespace SaturationMonoid.PhysicsCore.StageNineStageEightFirstJet

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7MotherGaugeAction
open SU7MotherSourceConfiguration
open DiracExteriorMatterLocalGaugeLink
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource

noncomputable section

def stageEightMotherConnection
    (source : SmoothUnifiedSource) : SU7MotherGaugeConnection :=
  sourceMotherConnection source.legacy

/-- Antisymmetric coordinate form of the six Stage-8 exterior-derivative
components, in order `(01,02,03,23,31,12)`. -/
def stageEightExteriorDerivativeComponent
    (source : SmoothUnifiedSource)
    (first second : LorentzianIndex) : SU7MotherLieMatrix :=
  if first = 0 ∧ second = 1 then
    (stageEightMotherConnection source).exteriorDerivative 0
  else if first = 1 ∧ second = 0 then
    -(stageEightMotherConnection source).exteriorDerivative 0
  else if first = 0 ∧ second = 2 then
    (stageEightMotherConnection source).exteriorDerivative 1
  else if first = 2 ∧ second = 0 then
    -(stageEightMotherConnection source).exteriorDerivative 1
  else if first = 0 ∧ second = 3 then
    (stageEightMotherConnection source).exteriorDerivative 2
  else if first = 3 ∧ second = 0 then
    -(stageEightMotherConnection source).exteriorDerivative 2
  else if first = 2 ∧ second = 3 then
    (stageEightMotherConnection source).exteriorDerivative 3
  else if first = 3 ∧ second = 2 then
    -(stageEightMotherConnection source).exteriorDerivative 3
  else if first = 3 ∧ second = 1 then
    (stageEightMotherConnection source).exteriorDerivative 4
  else if first = 1 ∧ second = 3 then
    -(stageEightMotherConnection source).exteriorDerivative 4
  else if first = 1 ∧ second = 2 then
    (stageEightMotherConnection source).exteriorDerivative 5
  else if first = 2 ∧ second = 1 then
    -(stageEightMotherConnection source).exteriorDerivative 5
  else 0

theorem stageEightExteriorDerivativeComponent_antisymm
    (source : SmoothUnifiedSource)
    (first second : LorentzianIndex) :
    stageEightExteriorDerivativeComponent source first second =
      -stageEightExteriorDerivativeComponent source second first := by
  fin_cases first <;> fin_cases second <;>
    simp [stageEightExteriorDerivativeComponent]

@[simp] theorem stageEightExteriorDerivativeComponent_pair
    (source : SmoothUnifiedSource) (pair : Fin 6) :
    stageEightExteriorDerivativeComponent source
        (pairFirst pair) (pairSecond pair) =
      (stageEightMotherConnection source).exteriorDerivative pair := by
  fin_cases pair <;>
    simp [stageEightExteriorDerivativeComponent, pairFirst, pairSecond]

/-- Smooth affine extension whose origin value and antisymmetric first jet are
the exact Stage-8 mother connection data. -/
def generatedUnifiedMotherPotential
    (source : SmoothUnifiedSource)
    (point : BasePoint) (direction : LorentzianIndex) :
    SU7MotherLieMatrix :=
  (stageEightMotherConnection source).potential direction +
    (1 / 2 : ℝ) •
      ∑ derivative : LorentzianIndex,
        point derivative •
          stageEightExteriorDerivativeComponent source derivative direction

@[simp] theorem generatedUnifiedMotherPotential_origin
    (source : SmoothUnifiedSource) (direction : LorentzianIndex) :
    generatedUnifiedMotherPotential source 0 direction =
      (stageEightMotherConnection source).potential direction := by
  simp [generatedUnifiedMotherPotential]

/-- Exact affine increment law, hence the actual derivative of the generated
connection field. -/
theorem generatedUnifiedMotherPotential_increment
    (source : SmoothUnifiedSource) (point displacement : BasePoint)
    (direction : LorentzianIndex) :
    generatedUnifiedMotherPotential source (point + displacement) direction =
      generatedUnifiedMotherPotential source point direction +
        (1 / 2 : ℝ) •
          ∑ derivative : LorentzianIndex,
            displacement derivative •
              stageEightExteriorDerivativeComponent source derivative
                direction := by
  change
    (stageEightMotherConnection source).potential direction +
        (1 / 2 : ℝ) •
          ∑ derivative,
            (point derivative + displacement derivative) •
              stageEightExteriorDerivativeComponent source derivative
                direction =
      ((stageEightMotherConnection source).potential direction +
        (1 / 2 : ℝ) •
          ∑ derivative,
            point derivative •
              stageEightExteriorDerivativeComponent source derivative
                direction) +
        (1 / 2 : ℝ) •
          ∑ derivative,
            displacement derivative •
              stageEightExteriorDerivativeComponent source derivative
                direction
  rw [show
    (∑ derivative,
      (point derivative + displacement derivative) •
        stageEightExteriorDerivativeComponent source derivative direction) =
      (∑ derivative,
        point derivative •
          stageEightExteriorDerivativeComponent source derivative direction) +
      ∑ derivative,
        displacement derivative •
          stageEightExteriorDerivativeComponent source derivative direction by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro derivative _
      rw [add_smul]]
  module

def generatedUnifiedMotherCurvatureAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (first second : LorentzianIndex) : SU7MotherLieMatrix :=
  stageEightExteriorDerivativeComponent source first second +
    suLieBracket
      (generatedUnifiedMotherPotential source point first)
      (generatedUnifiedMotherPotential source point second)

/-- At the origin, the smooth generated curvature is exactly the Stage-8
non-Abelian mother curvature. -/
@[simp] theorem generatedUnifiedMotherCurvatureAt_origin_pair
    (source : SmoothUnifiedSource) (pair : Fin 6) :
    generatedUnifiedMotherCurvatureAt source 0
        (pairFirst pair) (pairSecond pair) =
      motherCurvature (stageEightMotherConnection source) pair := by
  simp [generatedUnifiedMotherCurvatureAt, motherCurvature]

def UnifiedMotherPotentialComponentwiseSmooth
    (source : SmoothUnifiedSource) : Prop :=
  ∀ direction row column,
    ContDiff ℝ ⊤
      (fun point =>
        ((generatedUnifiedMotherPotential source point direction :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) row column))

theorem generatedUnifiedMotherPotential_componentwiseSmooth
    (source : SmoothUnifiedSource) :
    UnifiedMotherPotentialComponentwiseSmooth source := by
  intro direction row column
  change
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        (((stageEightMotherConnection source).potential direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) row column) +
          (1 / 2 : ℝ) •
            ∑ derivative : LorentzianIndex,
              (point derivative : ℂ) *
                ((stageEightExteriorDerivativeComponent source derivative
                    direction : SU7MotherLieMatrix) :
                  Matrix SU7MotherIndex SU7MotherIndex ℂ) row column)
  apply ContDiff.add contDiff_const
  change
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        ((1 / 2 : ℝ) : ℂ) *
          ∑ derivative : LorentzianIndex,
            (point derivative : ℂ) *
              ((stageEightExteriorDerivativeComponent source derivative
                  direction : SU7MotherLieMatrix) :
                Matrix SU7MotherIndex SU7MotherIndex ℂ) row column)
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro derivative _derivativeInUniv
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  · exact contDiff_const

def generatedUnifiedMotherTransportFirstJet
    (source : SmoothUnifiedSource) (direction : LorentzianIndex) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  1 + ((stageEightMotherConnection source).potential direction :
    Matrix SU7MotherIndex SU7MotherIndex ℂ)

/-- Stage 8 `1+A` is exactly the first jet of the smooth matrix-exponential
transport generated from the same source and connection. -/
theorem generatedUnifiedMotherTransportFirstJet_eq_stageEightLink
    (source : SmoothUnifiedSource) (direction : LorentzianIndex) :
    generatedUnifiedMotherTransportFirstJet source direction =
      motherLinkFamilyOfConnection (stageEightMotherConnection source)
        direction :=
  rfl

theorem positive_generatedUnifiedMotherCurvature_nonzero :
    generatedUnifiedMotherCurvatureAt positiveSmoothUnifiedSource 0
        (pairFirst 0) (pairSecond 0) ≠ 0 := by
  rw [generatedUnifiedMotherCurvatureAt_origin_pair]
  intro curvatureZero
  have colorZero := congrArg motherColorCoordinate curvatureZero
  change
    motherColorCoordinate
        (motherCurvature (sourceMotherConnection canonicalPhysicalSource) 0) =
      motherColorCoordinate 0 at colorZero
  rw [sourceMother_colorCoordinate,
    canonicalPhysicalSource_gaugeCurvature_component] at colorZero
  norm_num at colorZero

/-- Zero/flat fake regression: the smooth extension cannot have zero origin
curvature while remaining the exact Stage-8 first jet. -/
theorem zeroCurvatureFake_rejected
    (candidate : BasePoint → LorentzianIndex → LorentzianIndex →
      SU7MotherLieMatrix)
    (candidate_zero : candidate 0 (pairFirst 0) (pairSecond 0) = 0) :
    candidate ≠ generatedUnifiedMotherCurvatureAt
        positiveSmoothUnifiedSource := by
  intro equality
  have atOrigin := congrFun
    (congrFun (congrFun equality 0) (pairFirst 0)) (pairSecond 0)
  rw [candidate_zero] at atOrigin
  exact positive_generatedUnifiedMotherCurvature_nonzero atOrigin.symm

/-- S9-A4 checkpoint: one source produces a smooth mother connection whose
origin curvature and affine first jet exactly recover Stage 8. -/
theorem positiveSource_generates_smoothMotherConnection_with_stageEightFirstJet :
    UnifiedMotherPotentialComponentwiseSmooth positiveSmoothUnifiedSource ∧
      generatedUnifiedMotherCurvatureAt positiveSmoothUnifiedSource 0
          (pairFirst 0) (pairSecond 0) ≠ 0 ∧
      (∀ direction,
        generatedUnifiedMotherPotential positiveSmoothUnifiedSource 0
            direction =
          (stageEightMotherConnection positiveSmoothUnifiedSource).potential
            direction) ∧
      (∀ direction,
        generatedUnifiedMotherTransportFirstJet
            positiveSmoothUnifiedSource direction =
          motherLinkFamilyOfConnection
              (stageEightMotherConnection positiveSmoothUnifiedSource)
            direction) := by
  exact ⟨generatedUnifiedMotherPotential_componentwiseSmooth
      positiveSmoothUnifiedSource,
    positive_generatedUnifiedMotherCurvature_nonzero,
    generatedUnifiedMotherPotential_origin
      positiveSmoothUnifiedSource,
    generatedUnifiedMotherTransportFirstJet_eq_stageEightLink
      positiveSmoothUnifiedSource⟩

end

end SaturationMonoid.PhysicsCore.StageNineStageEightFirstJet
