import H0mework.Physics.GaugeAction.P286CanonicalDiagonalActionPrincipal
import H0mework.Physics.Cauchy.P286ActionCauchySplit

/-!
# Radial-quartic P286 action principal

This module constructs one globally defined radial-quartic temporal connection
field and proves that its actual Hessian generates the radial-quadratic P286
action forcing at every spacetime point.  Its coefficient is fixed by the
three-dimensional radial Laplacian: the complete P286 principal response of
`r^4 / 40` is `r^2`.

No residual coordinate, support branch, target jet, supplied integrability
receipt, or free coefficient enters the constructor.  The theorem is a
whole-field action-principal producer; installing it into a Stage-9 current
and closing the coupled scalar/matter changed reads remain downstream work.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286RadialQuarticActionPrincipal

open StageNineHolonomicField
open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Spatial Euclidean metric, regarded as a covector-valued linear map. -/
def p286SpatialMetricCovectorOperator :
    BasePoint →L[ℝ] (BasePoint →L[ℝ] ℝ) :=
  ∑ axis : Fin 3,
    (p286BaseCoordinate axis.succ).smulRight
      (p286BaseCoordinate axis.succ)

/-- Squared radius in the three canonical spatial directions. -/
def p286SpatialRadiusSquared (point : BasePoint) : ℝ :=
  p286SpatialMetricCovectorOperator point point

/-- Spatial contraction with one fixed base point. -/
def p286SpatialRadialCovector (point : BasePoint) : BasePoint →L[ℝ] ℝ :=
  p286SpatialMetricCovectorOperator point

/-- Spatial Euclidean metric with values in one temporal P286 one-form. -/
def p286SpatialMetricTemporalJetAmbient
    (charge : P286CoordinateCarrier) : P286ConnectionSecondJetAmbient :=
  ∑ axis : Fin 3,
    (p286BaseCoordinate axis.succ).smulRight
      ((p286BaseCoordinate axis.succ).smulRight
        (p286TemporalGaugeOneForm charge))

/-- Hessian of `(r^4 / 40) · A₀(charge)`. -/
def p286RadialQuarticTemporalSecondJetAmbient
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    P286ConnectionSecondJetAmbient :=
  (1 / 5 : ℝ) •
      (p286SpatialRadialCovector point).smulRight
        ((p286SpatialRadialCovector point).smulRight
          (p286TemporalGaugeOneForm charge)) +
    (p286SpatialRadiusSquared point / 10 : ℝ) •
      p286SpatialMetricTemporalJetAmbient charge

theorem p286RadialQuarticTemporalSecondJetAmbient_symmetric
    (charge : P286CoordinateCarrier) (point first second : BasePoint) :
    p286RadialQuarticTemporalSecondJetAmbient charge point first second =
      p286RadialQuarticTemporalSecondJetAmbient charge point second first := by
  unfold p286RadialQuarticTemporalSecondJetAmbient
    p286SpatialMetricTemporalJetAmbient
  change
    (1 / 5 : ℝ) •
          (p286SpatialRadialCovector point first •
            (p286SpatialRadialCovector point second •
              p286TemporalGaugeOneForm charge)) +
        (p286SpatialRadiusSquared point / 10 : ℝ) •
          (∑ axis : Fin 3,
            first axis.succ •
              (second axis.succ • p286TemporalGaugeOneForm charge)) =
      (1 / 5 : ℝ) •
          (p286SpatialRadialCovector point second •
            (p286SpatialRadialCovector point first •
              p286TemporalGaugeOneForm charge)) +
        (p286SpatialRadiusSquared point / 10 : ℝ) •
          (∑ axis : Fin 3,
            second axis.succ •
              (first axis.succ • p286TemporalGaugeOneForm charge))
  congr 1
  · module
  · apply congrArg (fun value : P286GaugeOneForm =>
      (p286SpatialRadiusSquared point / 10 : ℝ) • value)
    apply Finset.sum_congr rfl
    intro axis _
    module

def p286RadialQuarticTemporalSecondJet
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    P286HolonomicConnectionSecondJet :=
  ⟨p286RadialQuarticTemporalSecondJetAmbient charge point,
    p286RadialQuarticTemporalSecondJetAmbient_symmetric charge point⟩

theorem p286SpatialRadialCovector_apply
    (point direction : BasePoint) :
    p286SpatialRadialCovector point direction =
      ∑ axis : Fin 3, point axis.succ * direction axis.succ := by
  simp [p286SpatialRadialCovector, p286SpatialMetricCovectorOperator,
    p286BaseCoordinate_apply]

theorem p286SpatialRadiusSquared_hasFDerivAt (point : BasePoint) :
    HasFDerivAt p286SpatialRadiusSquared
      (2 • p286SpatialRadialCovector point) point := by
  have rawDerivative :=
    p286SpatialMetricCovectorOperator.hasFDerivAt_of_bilinear
      (hasFDerivAt_id (x := point)) (hasFDerivAt_id (x := point))
  have derivativeEquality :
      p286SpatialMetricCovectorOperator.precompR BasePoint point
          (ContinuousLinearMap.id ℝ BasePoint) +
        p286SpatialMetricCovectorOperator.precompL BasePoint
          (ContinuousLinearMap.id ℝ BasePoint) point =
      2 • p286SpatialRadialCovector point := by
    ext direction
    simp [p286SpatialRadialCovector, p286SpatialMetricCovectorOperator,
      p286BaseCoordinate_apply]
    have swapped :
        (∑ axis : Fin 3, direction axis.succ * point axis.succ) =
          ∑ axis : Fin 3, point axis.succ * direction axis.succ := by
      apply Finset.sum_congr rfl
      intro axis _
      ring
    rw [swapped]
    ring
  change HasFDerivAt (fun candidate =>
    p286SpatialMetricCovectorOperator candidate candidate)
      (2 • p286SpatialRadialCovector point) point
  rw [← derivativeEquality]
  exact rawDerivative

theorem p286SpatialRadiusSquared_contDiff :
    ContDiff ℝ ∞ p286SpatialRadiusSquared := by
  change ContDiff ℝ ∞ fun point : BasePoint =>
    p286SpatialMetricCovectorOperator point point
  exact p286SpatialMetricCovectorOperator.contDiff.clm_apply contDiff_id

/-- The coefficient of the global radial-quartic temporal connection field. -/
def p286SpatialRadialQuarticCoefficient (point : BasePoint) : ℝ :=
  (1 / 40 : ℝ) * p286SpatialRadiusSquared point ^ 2

theorem p286SpatialRadialQuarticCoefficient_hasFDerivAt
    (point : BasePoint) :
    HasFDerivAt p286SpatialRadialQuarticCoefficient
      ((p286SpatialRadiusSquared point / 10 : ℝ) •
        p286SpatialRadialCovector point) point := by
  have rawDerivative :=
    ((p286SpatialRadiusSquared_hasFDerivAt point).pow 2).const_mul
      (1 / 40 : ℝ)
  change HasFDerivAt
    (fun candidate =>
      (1 / 40 : ℝ) * p286SpatialRadiusSquared candidate ^ 2)
    ((p286SpatialRadiusSquared point / 10 : ℝ) •
      p286SpatialRadialCovector point) point
  apply rawDerivative.congr_fderiv
  ext direction
  simp
  ring

theorem p286SpatialRadialQuarticCoefficient_contDiff :
    ContDiff ℝ ∞ p286SpatialRadialQuarticCoefficient := by
  change ContDiff ℝ ∞ fun point : BasePoint =>
    (1 / 40 : ℝ) * p286SpatialRadiusSquared point ^ 2
  exact
    (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => (1 / 40 : ℝ)).mul
      (p286SpatialRadiusSquared_contDiff.pow 2)

/-- Global field whose Hessian realizes the radial-quartic action principal. -/
def p286RadialQuarticTemporalConnection
    (charge : P286CoordinateCarrier) : BasePoint → P286GaugeOneForm :=
  fun point =>
    p286SpatialRadialQuarticCoefficient point •
      p286TemporalGaugeOneForm charge

/-- The radial-quadratic scalar multiplying the first-jet covector. -/
def p286SpatialRadialQuadraticScale (point : BasePoint) : ℝ :=
  (1 / 10 : ℝ) * p286SpatialRadiusSquared point

theorem p286SpatialRadialQuadraticScale_hasFDerivAt
    (point : BasePoint) :
    HasFDerivAt p286SpatialRadialQuadraticScale
      ((1 / 5 : ℝ) • p286SpatialRadialCovector point) point := by
  have rawDerivative :=
    (p286SpatialRadiusSquared_hasFDerivAt point).const_mul (1 / 10 : ℝ)
  change HasFDerivAt
    (fun candidate => (1 / 10 : ℝ) * p286SpatialRadiusSquared candidate)
    ((1 / 5 : ℝ) • p286SpatialRadialCovector point) point
  apply rawDerivative.congr_fderiv
  ext direction
  simp
  ring

theorem p286SpatialRadialCovector_hasFDerivAt (point : BasePoint) :
    HasFDerivAt p286SpatialRadialCovector
      p286SpatialMetricCovectorOperator point := by
  exact p286SpatialMetricCovectorOperator.hasFDerivAt

/-- Continuous linear embedding of a scalar covector into the fixed temporal
P286 one-form direction. -/
def p286TemporalConnectionJetEmbedding
    (charge : P286CoordinateCarrier) :
    (BasePoint →L[ℝ] ℝ) →L[ℝ]
      (BasePoint →L[ℝ] P286GaugeOneForm) :=
  (ContinuousLinearMap.flip
    (ContinuousLinearMap.smulRightL ℝ BasePoint P286GaugeOneForm))
      (p286TemporalGaugeOneForm charge)

/-- Exact first jet of the global radial-quartic connection field. -/
def p286RadialQuarticTemporalFirstJet
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    BasePoint →L[ℝ] P286GaugeOneForm :=
  p286TemporalConnectionJetEmbedding charge
    (p286SpatialRadialQuadraticScale point •
      p286SpatialRadialCovector point)

theorem p286RadialQuarticTemporalConnection_hasFDerivAt
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    HasFDerivAt (p286RadialQuarticTemporalConnection charge)
      (p286RadialQuarticTemporalFirstJet charge point) point := by
  have rawDerivative :=
    (p286SpatialRadialQuarticCoefficient_hasFDerivAt point).smul_const
      (p286TemporalGaugeOneForm charge)
  change HasFDerivAt
    (fun candidate =>
      p286SpatialRadialQuarticCoefficient candidate •
        p286TemporalGaugeOneForm charge)
    (p286RadialQuarticTemporalFirstJet charge point) point
  apply rawDerivative.congr_fderiv
  ext direction formDirection
  simp [p286RadialQuarticTemporalFirstJet,
    p286SpatialRadialQuadraticScale,
    p286TemporalConnectionJetEmbedding]
  ring

theorem p286RadialQuarticTemporalConnection_contDiff
    (charge : P286CoordinateCarrier) :
    ContDiff ℝ ∞ (p286RadialQuarticTemporalConnection charge) := by
  exact p286SpatialRadialQuarticCoefficient_contDiff.smul_const
    (p286TemporalGaugeOneForm charge)

/-- Hessian of the radial-quartic scalar coefficient before embedding it in
the temporal P286 one-form. -/
def p286SpatialRadialQuarticCovectorSecondJet
    (point : BasePoint) : BasePoint →L[ℝ] (BasePoint →L[ℝ] ℝ) :=
  p286SpatialRadialQuadraticScale point •
      p286SpatialMetricCovectorOperator +
    ((1 / 5 : ℝ) • p286SpatialRadialCovector point).smulRight
      (p286SpatialRadialCovector point)

theorem p286SpatialRadialScaledCovector_hasFDerivAt
    (point : BasePoint) :
    HasFDerivAt
      (fun candidate =>
        p286SpatialRadialQuadraticScale candidate •
          p286SpatialRadialCovector candidate)
      (p286SpatialRadialQuarticCovectorSecondJet point) point := by
  exact
    (p286SpatialRadialQuadraticScale_hasFDerivAt point).smul
      (p286SpatialRadialCovector_hasFDerivAt point)

theorem p286TemporalEmbedding_comp_radialQuarticCovectorSecondJet
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    (p286TemporalConnectionJetEmbedding charge).comp
        (p286SpatialRadialQuarticCovectorSecondJet point) =
      p286RadialQuarticTemporalSecondJetAmbient charge point := by
  ext first second formDirection
  simp [p286TemporalConnectionJetEmbedding,
    p286SpatialRadialQuarticCovectorSecondJet,
    p286RadialQuarticTemporalSecondJetAmbient,
    p286SpatialRadialQuadraticScale,
    p286SpatialMetricTemporalJetAmbient,
    p286SpatialMetricCovectorOperator,
    ContinuousLinearMap.flip_apply]
  ring

/-- The displayed radial-quartic second jet is the actual Hessian of one
globally defined connection field at every spacetime point. -/
theorem p286RadialQuarticTemporalFirstJet_hasFDerivAt
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    HasFDerivAt (p286RadialQuarticTemporalFirstJet charge)
      (p286RadialQuarticTemporalSecondJetAmbient charge point) point := by
  have embeddedDerivative :=
    (p286TemporalConnectionJetEmbedding charge).hasFDerivAt.comp point
      (p286SpatialRadialScaledCovector_hasFDerivAt point)
  change HasFDerivAt
    (fun candidate =>
      p286TemporalConnectionJetEmbedding charge
        (p286SpatialRadialQuadraticScale candidate •
          p286SpatialRadialCovector candidate))
    (p286RadialQuarticTemporalSecondJetAmbient charge point) point
  rw [← p286TemporalEmbedding_comp_radialQuarticCovectorSecondJet]
  exact embeddedDerivative

theorem p286RadialQuarticTemporalConnection_secondFrechetJet
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    fderiv ℝ (fderiv ℝ (p286RadialQuarticTemporalConnection charge)) point =
      p286RadialQuarticTemporalSecondJetAmbient charge point := by
  have firstDerivative :
      fderiv ℝ (p286RadialQuarticTemporalConnection charge) =
        p286RadialQuarticTemporalFirstJet charge := by
    funext candidate
    exact (p286RadialQuarticTemporalConnection_hasFDerivAt
      charge candidate).fderiv
  rw [firstDerivative]
  exact (p286RadialQuarticTemporalFirstJet_hasFDerivAt charge point).fderiv

/-- Evaluation form of the Hessian identity used by whole-occurrence
realization predicates. -/
theorem p286RadialQuarticTemporalConnection_secondFrechetJet_apply
    (charge : P286CoordinateCarrier) (point outerDirection innerDirection : BasePoint) :
    (fderiv ℝ
        (fun candidate =>
          fderiv ℝ (p286RadialQuarticTemporalConnection charge) candidate
            innerDirection)
        point) outerDirection =
      p286RadialQuarticTemporalSecondJetAmbient charge point
        outerDirection innerDirection := by
  let evaluation :
      (BasePoint →L[ℝ] P286GaugeOneForm) →L[ℝ] P286GaugeOneForm :=
    ContinuousLinearMap.apply ℝ P286GaugeOneForm innerDirection
  have firstDerivative :
      fderiv ℝ (p286RadialQuarticTemporalConnection charge) =
        p286RadialQuarticTemporalFirstJet charge := by
    funext candidate
    exact (p286RadialQuarticTemporalConnection_hasFDerivAt
      charge candidate).fderiv
  rw [firstDerivative]
  have evaluatedDerivative : HasFDerivAt
      (fun candidate =>
        evaluation (p286RadialQuarticTemporalFirstJet charge candidate))
      (evaluation.comp
        (p286RadialQuarticTemporalSecondJetAmbient charge point)) point := by
    exact evaluation.hasFDerivAt.comp point
      (p286RadialQuarticTemporalFirstJet_hasFDerivAt charge point)
  change
    (fderiv ℝ
      (fun candidate =>
        evaluation (p286RadialQuarticTemporalFirstJet charge candidate))
      point) outerDirection = _
  rw [evaluatedDerivative.fderiv]
  rfl

theorem p286RadialQuarticTemporalSecondJet_response
    (charge : P286CoordinateCarrier) (point : BasePoint) :
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286RadialQuarticTemporalSecondJet charge point) =
      p286GaugeOneFormPairingDual
        (p286SpatialRadiusSquared point •
          p286TemporalGaugeOneForm charge) := by
  apply LinearMap.ext
  intro direction
  rw [p286HolonomicSecondJetEulerLagrangeResponse_apply]
  unfold p286HolonomicSecondJetBFDivergenceResponseValue
  simp_rw [p286HolonomicSecondJetBFDivergenceResponseTerm_normalForm]
  simp [p286RadialQuarticTemporalSecondJet,
    p286RadialQuarticTemporalSecondJetAmbient,
    p286SpatialMetricTemporalJetAmbient,
    p286SpatialRadiusSquared, p286SpatialRadialCovector,
    p286SpatialMetricCovectorOperator,
    p286HolonomicSecondJetCurvatureSymbol,
    p286HolonomicSecondJetOrderedCurvatureSymbol,
    p286GaugeExteriorDerivativeDirection,
    p286GaugeOneFormPairingDual,
    p286TemporalGaugeOneForm,
    ContinuousLinearMap.smulRight_apply,
    p286BaseCoordinate_apply, coordinateDirection,
    canonicalLorentzianTimeDirection,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_neg_left_local,
    p286CoordinateLiePairing_neg_right_local,
    Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_six]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineP286RadialQuarticActionPrincipal
