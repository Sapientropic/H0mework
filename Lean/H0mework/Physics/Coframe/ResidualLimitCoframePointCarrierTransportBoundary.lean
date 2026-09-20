import H0mework.Physics.Coframe.ResidualLimitCoframeBalanceDecision

/-!
# S9-C3h45: synchronized coframe point-carrier transport boundary

This module classifies one explicit existing-field carrier.  The coframe,
gravity auxiliary, and gravity curvature are scaled together so that the two
strong algebraic gravity equations remain exact.  The actual P286 and vacuum
point values are retained.  No new field, coupling, source slot, equation
receipt, or stationarity witness is introduced.

The carrier is deliberately narrow: it decides the canonical radial response
class and the already known multiplier response-null class.  It does not claim
that the whole Stage-9 point-field carrier is empty.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitCoframePointCarrierTransportBoundary

open AffineRelaxation
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineGravityMultiplierResidualNoninjectivity
open StageNinePlebanskiMultiplierVariation
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitCoframeBalanceDecision
open SU7MotherGaugeTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Existing-field radial synchronization.  Gravity `B` and `F` follow the
quadratic coframe weight forced by simplicity and the constitutive equation.
Every other point-field coordinate is retained from the actual reference
origin field. -/
def synchronizedRadialPointField (scalar : ℝ) :
    StageNineContinuumPointField :=
  { referenceOriginField with
    coframe := radialCoframe scalar
    gravityCurvature := scalar ^ 2 • referenceOriginField.gravityCurvature
    gravityAuxiliary := scalar ^ 2 • referenceOriginField.gravityAuxiliary }

@[simp] theorem synchronizedRadialPointField_coframe (scalar : ℝ) :
    (synchronizedRadialPointField scalar).coframe = radialCoframe scalar :=
  rfl

@[simp] theorem synchronizedRadialPointField_gravityCurvature (scalar : ℝ) :
    (synchronizedRadialPointField scalar).gravityCurvature =
      scalar ^ 2 • referenceOriginField.gravityCurvature :=
  rfl

@[simp] theorem synchronizedRadialPointField_gravityAuxiliary (scalar : ℝ) :
    (synchronizedRadialPointField scalar).gravityAuxiliary =
      scalar ^ 2 • referenceOriginField.gravityAuxiliary :=
  rfl

@[simp] theorem synchronizedRadialPointField_multiplier (scalar : ℝ) :
    (synchronizedRadialPointField scalar).gravitySimplicityMultiplier = 0 :=
  referencePointField_multiplier_zero

/-- The synchronized carrier stays on the strong simplicity shell without a
stored shell receipt. -/
theorem synchronizedRadialPointField_simplicity (scalar : ℝ) :
    (synchronizedRadialPointField scalar).gravityAuxiliary =
      physicalIIPlusBivector (synchronizedRadialPointField scalar).coframe := by
  rw [synchronizedRadialPointField_gravityAuxiliary,
    synchronizedRadialPointField_coframe,
    referenceOriginField_gravityAuxiliary_eq_physical]
  exact (physicalIIPlusBivector_smul scalar (1 : LorentzianCoframe)).symm

/-- The same synchronization stays on the strong gravity-auxiliary shell. -/
theorem synchronizedRadialPointField_gravityConstitutive (scalar : ℝ) :
    (synchronizedRadialPointField scalar).gravityCurvature =
      gravityInternalDualEquiv
        (synchronizedRadialPointField scalar).gravityAuxiliary := by
  rw [synchronizedRadialPointField_gravityCurvature,
    synchronizedRadialPointField_gravityAuxiliary,
    referenceOriginField_gravityCurvature_eq_constitutive]
  exact (gravityInternalDualEquiv.map_smul
    (scalar ^ 2) referenceOriginField.gravityAuxiliary).symm

/-- The retained P286 point values remain on their constitutive shell because
the radial coframe Hodge operator is invariant on every nonzero scale. -/
theorem synchronizedRadialPointField_p286Constitutive
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    liftGaugeTwoFormOperator
        ((1 / 2 : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (synchronizedRadialPointField scalar).coframe)
        referenceP286AuxiliaryCoordinate =
      referenceP286CurvatureCoordinate := by
  rw [synchronizedRadialPointField_coframe,
    radialCoframe_spacetimeHodge scalar nonzero]
  have hodgeEq :
      lorentzianCoframeHodgeEquiv.toLinearMap =
        lorentzianCoframeHodge := rfl
  rw [hodgeEq]
  exact referenceP286CoupledHodgeAuxiliary_eq_curvature

/-! ## Density normal form on the synchronized radial carrier -/

theorem synchronizedRadialPointField_gravityBFDensity
    (fieldScalar candidateScalar : ℝ)
    (candidateNonzero : candidateScalar ≠ 0) :
    generatedGravityBFDensity
        (withCoframe (synchronizedRadialPointField fieldScalar)
          (radialCoframe candidateScalar)) =
      fieldScalar ^ 4 * candidateScalar ^ 4 * (-3 : ℝ) := by
  unfold generatedGravityBFDensity
  simp only [withCoframe, synchronizedRadialPointField]
  rw [gravityInternalDualEquiv.map_smul]
  simp_rw [gravitySpacetimeHodge_smul]
  rw [gravityCoframePairing_smul_left,
    gravityCoframePairing_smul_right,
    gravityCoframePairing_smul_left,
    gravityCoframePairing_smul_right]
  rw [gravitySpacetimeHodge_radial candidateScalar candidateNonzero,
    gravitySpacetimeHodge_radial candidateScalar candidateNonzero]
  rw [gravityCoframePairing_radial, gravityCoframePairing_radial]
  have reference := referenceOriginField_gravityBFDensity_eq_neg_three
  unfold generatedGravityBFDensity at reference
  rw [referenceOriginField_coframe_eq_one] at reference
  linear_combination fieldScalar ^ 4 * candidateScalar ^ 4 * reference

theorem synchronizedRadialPointField_gravitySectorLocalDensity
    (fieldScalar candidateScalar : ℝ)
    (candidateNonzero : candidateScalar ≠ 0) :
    coframeGravitySectorLocalDensity
        (synchronizedRadialPointField fieldScalar)
        (radialCoframe candidateScalar) =
      fieldScalar ^ 4 * candidateScalar ^ 8 * (-3 : ℝ) := by
  unfold coframeGravitySectorLocalDensity
  have volumeEq :
      generatedVolumeDensity
          (withCoframe (synchronizedRadialPointField fieldScalar)
            (radialCoframe candidateScalar)) = candidateScalar ^ 4 := by
    change abs (Matrix.det (radialCoframe candidateScalar)) =
      candidateScalar ^ 4
    simpa [generatedVolumeDensity, withCoframe] using
      referenceOriginField_radial_volume candidateScalar
  rw [volumeEq]
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero]
  · rw [synchronizedRadialPointField_gravityBFDensity
      fieldScalar candidateScalar candidateNonzero]
    ring
  · exact synchronizedRadialPointField_multiplier fieldScalar

theorem synchronizedRadialPointField_gaugeSectorLocalDensity
    (fieldScalar candidateScalar : ℝ)
    (candidateNonzero : candidateScalar ≠ 0) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        (synchronizedRadialPointField fieldScalar)
        (radialCoframe candidateScalar) =
      candidateScalar ^ 8 * (-(5 / 16 : ℝ)) := by
  change coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      referenceOriginField (radialCoframe candidateScalar) = _
  exact referenceOriginField_gaugeSectorLocalDensity_radial
    candidateScalar candidateNonzero

theorem synchronizedRadialPointField_scalarSectorLocalDensity_zero
    (fieldScalar : ℝ) (coframe : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField fieldScalar) coframe = 0 := by
  change coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
      referenceOriginField coframe = 0
  exact referenceOriginField_scalarSectorLocalDensity_zero coframe

theorem synchronizedRadialPointField_matterSectorLocalDensity_zero
    (fieldScalar : ℝ) (coframe : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField fieldScalar) coframe = 0 := by
  change coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      referenceOriginField coframe = 0
  exact referenceOriginField_matterSectorLocalDensity_zero coframe

theorem synchronizedRadialPointField_coframeLocalDensity
    (fieldScalar candidateScalar : ℝ)
    (candidateNonzero : candidateScalar ≠ 0) :
    coframeLocalDensity positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField fieldScalar)
        (radialCoframe candidateScalar) =
      -(3 * fieldScalar ^ 4 + 5 / 16 : ℝ) * candidateScalar ^ 8 := by
  rw [coframeLocalDensity_eq_sector_sum,
    synchronizedRadialPointField_gravitySectorLocalDensity
      fieldScalar candidateScalar candidateNonzero,
    synchronizedRadialPointField_gaugeSectorLocalDensity
      fieldScalar candidateScalar candidateNonzero,
    synchronizedRadialPointField_scalarSectorLocalDensity_zero,
    synchronizedRadialPointField_matterSectorLocalDensity_zero]
  ring

/-! ## Coframe response and zero-fiber boundary -/

theorem synchronizedRadialPointField_coframeStress_identity
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField scalar)
        (1 : LorentzianCoframe) =
      -8 * (3 * scalar ^ 4 + 5 / 16 : ℝ) * scalar ^ 7 := by
  have fieldNondegenerate :
      Matrix.det (synchronizedRadialPointField scalar).coframe ≠ 0 := by
    simpa [synchronizedRadialPointField, radialCoframe,
      Matrix.det_smul] using pow_ne_zero 4 nonzero
  have outer := coframeLocalDensity_hasFDerivAt
    positiveSmoothUnifiedSource 0
    (synchronizedRadialPointField scalar) fieldNondegenerate
  have identityDerivative := hasDerivAt_id (x := scalar)
  have radialDerivative := identityDerivative.smul_const
    (1 : LorentzianCoframe)
  have radialDerivativeValue :
      (1 : ℝ) • (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) := by simp
  have radialDerivativeAtScalar :=
    radialDerivative.congr_deriv radialDerivativeValue
  have pointEquality :
      (synchronizedRadialPointField scalar).coframe =
        radialCoframe scalar := rfl
  have composed := outer.comp_hasDerivAt_of_eq scalar
    radialDerivativeAtScalar pointEquality
  have polynomial := (identityDerivative.pow 8).const_mul
    (-(3 * scalar ^ 4 + 5 / 16 : ℝ))
  have formulaEventually : Filter.EventuallyEq (nhds scalar)
      (fun candidateScalar : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0
          (synchronizedRadialPointField scalar)
          (radialCoframe candidateScalar))
      (fun candidateScalar : ℝ =>
        -(3 * scalar ^ 4 + 5 / 16 : ℝ) * candidateScalar ^ 8) := by
    filter_upwards [eventually_ne_nhds nonzero] with candidate candidateNonzero
    exact synchronizedRadialPointField_coframeLocalDensity
      scalar candidate candidateNonzero
  have exactDerivative := polynomial.congr_of_eventuallyEq formulaEventually
  have derivativeEquality := composed.unique exactDerivative
  norm_num at derivativeEquality
  calc
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField scalar)
        (1 : LorentzianCoframe) =
      (-(5 / 16 : ℝ) + -(3 * scalar ^ 4)) * (8 * scalar ^ 7) :=
        derivativeEquality
    _ = -8 * (3 * scalar ^ 4 + 5 / 16 : ℝ) * scalar ^ 7 := by
      ring

/-- Every nondegenerate member of the synchronized radial algebraic carrier
misses the coframe zero fiber. -/
theorem synchronizedRadialPointField_coframeStress_ne_zero
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField scalar) ≠ 0 := by
  intro stressZero
  have identityZero := congrArg
    (fun stress : LorentzianCoframe →L[ℝ] ℝ =>
      stress (1 : LorentzianCoframe)) stressZero
  rw [synchronizedRadialPointField_coframeStress_identity scalar nonzero]
    at identityZero
  have coefficientPositive :
      0 < (3 * scalar ^ 4 + 5 / 16 : ℝ) := by positivity
  have scalarPowNonzero : scalar ^ 7 ≠ 0 := pow_ne_zero 7 nonzero
  have valueNonzero :
      -8 * (3 * scalar ^ 4 + 5 / 16 : ℝ) * scalar ^ 7 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt coefficientPositive))
      scalarPowNonzero
  exact valueNonzero (by simpa using identityZero)

/-- At the only radial zero `scalar = 0`, the coframe is degenerate.  Hence
this carrier has no admissible coframe-stress zero. -/
theorem synchronizedRadialPointField_zeroFiber_implies_degenerate
    (scalar : ℝ)
    (stressZero :
      coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField scalar) = 0) :
    Matrix.det (synchronizedRadialPointField scalar).coframe = 0 := by
  by_contra determinantNonzero
  have scalarNonzero : scalar ≠ 0 := by
    intro scalarZero
    apply determinantNonzero
    simp [scalarZero, synchronizedRadialPointField, radialCoframe]
  exact synchronizedRadialPointField_coframeStress_ne_zero
    scalar scalarNonzero stressZero

/-! ## Source-keep and multiplier response-null diagnostics -/

theorem positiveSource_keep_eq_half :
    (1 - positiveSmoothUnifiedSource.legacy.sigma : ℝ) = 1 / 2 := by
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  ring

/-- The source-forced scalar keep does not lift by applying the same scalar
to the synchronized point-field carrier. -/
theorem halfScaledPointField_does_not_realize_coframeKeep :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (synchronizedRadialPointField (1 / 2 : ℝ))
        (1 : LorentzianCoframe) ≠
      (1 / 2 : ℝ) *
        coframeLocalStressCovector positiveSmoothUnifiedSource 0
          referenceOriginField (1 : LorentzianCoframe) := by
  rw [synchronizedRadialPointField_coframeStress_identity]
  · rw [referenceOriginField_coframeStress_identity_eq_neg_fiftyThree_halves]
    norm_num
  · norm_num

/-- The explicit multiplier response-null pair has identical coframe
residual but distinct existing point-field values. -/
theorem referenceMultiplierPair_same_coframeResidual_but_distinct :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (withGravitySimplicityMultiplier referenceOriginField
          (physicalBivectorCoordinateDirection 0 0)) =
      coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (withGravitySimplicityMultiplier referenceOriginField 0) ∧
    withGravitySimplicityMultiplier referenceOriginField
        (physicalBivectorCoordinateDirection 0 0) ≠
      withGravitySimplicityMultiplier referenceOriginField 0 := by
  constructor
  · exact coframeLocalStressCovector_coordinate_eq_zero_of_simplicity
      positiveSmoothUnifiedSource 0 referenceOriginField
      (by rw [referenceOriginField_coframe_eq_one]; simp)
      referencePointField_simplicity
  · intro equality
    have multiplierEquality := congrArg
      StageNineContinuumPointField.gravitySimplicityMultiplier equality
    have coordinateNonzero :
        physicalBivectorCoordinateDirection 0 0 ≠ 0 := by
      intro coordinateZero
      have componentZero := congrFun (congrFun coordinateZero 0) 0
      simp [physicalBivectorCoordinateDirection] at componentZero
    exact coordinateNonzero multiplierEquality

/-- There is no exact identity-preserving decoder from the coframe residual
alone on the explicit two-point multiplier carrier.  Choosing a representative
would be an extra branch choice, not residual transport. -/
theorem no_exact_pointField_decoder_from_coframeResidual
    (decode : (LorentzianCoframe →L[ℝ] ℝ) →
      StageNineContinuumPointField)
    (decodeCoordinate :
      decode (coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (withGravitySimplicityMultiplier referenceOriginField
          (physicalBivectorCoordinateDirection 0 0))) =
        withGravitySimplicityMultiplier referenceOriginField
          (physicalBivectorCoordinateDirection 0 0))
    (decodeZero :
      decode (coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (withGravitySimplicityMultiplier referenceOriginField 0)) =
        withGravitySimplicityMultiplier referenceOriginField 0) : False := by
  have sameResidual :=
    referenceMultiplierPair_same_coframeResidual_but_distinct.1
  apply referenceMultiplierPair_same_coframeResidual_but_distinct.2
  rw [← decodeCoordinate, ← decodeZero, sameResidual]

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitCoframePointCarrierTransportBoundary
