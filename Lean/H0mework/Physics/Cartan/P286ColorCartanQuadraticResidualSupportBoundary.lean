import H0mework.Physics.Cartan.P286ColorCartanConstitutiveResponse

/-!
# S9-C3h79: residual support beyond the color-Cartan projection

C3h78 canonically cancels the origin P286 Euler--Lagrange residual in the
color-Cartan, spacetime-zero test direction.  This module audits the same
quadratic existing-field family against the independent representation-derived
commutator probe.

The quadratic curvature jet is color-Cartan valued.  Its differential-momentum
increment is therefore orthogonal to the commutator probe, so the probe
residual remains exactly `-3` for every coordinate in the C3h78 family.  In
particular the residual-derived C3h78 repair is not a full P286 pointwise
solution.

This is a stable negative gate for the explicit quadratic color-Cartan carrier
class.  It does not assert that the current joint shell is empty, enumerate a
basis of the full residual functional, add a source parameter, or supply a
stationarity certificate.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorCartanQuadraticResidualSupportBoundary

open ProofFreeRicherAnholonomicSource
open StageNineConnectionSectorSourceBalance
open StageNineCoframeGravityGaugeRegularity
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineGravityAlgebraicKeepResponseP286Defect
open StageNineHolonomicField
open StageNineP286ColorCartanConstitutiveResponse
open StageNineP286ColorCartanOffsetBoundary
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineResidualLimitP286BFBalanceDecision
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem p286LieBracket_antisymm_local
    (first second : P286LieBlockData) :
    p286LieBracket first second = -p286LieBracket second first := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

private theorem p286LiePairing_self_bracket_zero_local
    (matrix residual : P286LieBlockData) :
    p286LiePairing matrix (p286LieBracket matrix residual) = 0 := by
  unfold p286LiePairing p286LieBracket
  rw [specialUnitaryLiePairing_self_bracket_zero,
    specialUnitaryLiePairing_self_bracket_zero]
  simp [hyperchargeLiePairing]

/-- The C3h78 curvature-jet value is orthogonal to the independent
commutator probe.  This representation fact is why the C3h78 repair cannot
transport that residual channel. -/
theorem colorCartanQuadraticCoordinate_pairing_commutatorProbe_eq_zero :
    p286CoordinateLiePairing colorCartanQuadraticCoordinate
        (p286CoordinateEquiv p286CommutatorProbeData) = 0 := by
  rw [p286CommutatorData_eq_mixing_cartan_local,
    p286LieBracket_antisymm_local]
  simp only [map_neg]
  rw [p286CoordinateLiePairing_neg_right_local]
  unfold colorCartanQuadraticCoordinate p286CoordinateLiePairing
  simp only [p286CoordinateEquiv.symm_apply_apply]
  rw [p286LiePairing_self_bracket_zero_local]
  norm_num

/-! ## Probe momentum normal forms -/

private theorem quadraticResponse_probeMomentum_direction_zero
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe)
        point = 0 := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]

private theorem quadraticResponse_probeMomentum_direction_one
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 0)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

private theorem quadraticResponse_probeMomentum_direction_two
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate parameter point 5)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

private theorem quadraticResponse_probeMomentum_direction_three
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate parameter point 4)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

private theorem canonicalResponse_probeMomentum_direction_zero
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe)
        point = 0 := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]

private theorem canonicalResponse_probeMomentum_direction_one
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 0)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

private theorem canonicalResponse_probeMomentum_direction_two
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 1 +
          point 2 • actualNativeCurvatureCoordinate point 5)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

private theorem canonicalResponse_probeMomentum_direction_three
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 2 -
          point 2 • actualNativeCurvatureCoordinate point 4)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

/-! ## The quadratic jet has zero response in the probe channel -/

private theorem quadraticResponse_probeMomentum_direction_zero_derivative
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe))
        0 0 = 0 := by
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe) =
        fun _ => 0 := by
    funext point
    exact quadraticResponse_probeMomentum_direction_zero parameter point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

private theorem canonicalResponse_probeMomentum_direction_zero_derivative :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe))
        0 0 = 0 := by
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe) =
        fun _ => 0 := by
    funext point
    exact canonicalResponse_probeMomentum_direction_zero point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

private theorem quadraticResponse_probeMomentum_direction_one_derivative_eq_canonical
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe))
        0 1 =
      fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe))
        0 1 := by
  let responseCurvature : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 0
  let canonicalCurvature : BasePoint → P286CoordinateCarrier := fun point =>
    actualNativeCurvatureCoordinate point 0
  let responsePairing : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (responseCurvature point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  let canonicalPairing : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (canonicalCurvature point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have responseCurvatureSmooth : ContDiff ℝ ∞ responseCurvature :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 0
  have responseCurvatureDifferentiable :
      DifferentiableAt ℝ responseCurvature 0 :=
    (responseCurvatureSmooth.differentiable (by simp)).differentiableAt
  have canonicalCurvatureDerivative :
      HasFDerivAt canonicalCurvature (actualNativeCurvatureFDeriv 0) 0 :=
    actualNativeCurvatureCoordinate_hasFDerivAt_origin 0
  have responsePairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        responseCurvatureDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have canonicalPairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear canonicalCurvatureDerivative
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have responsePairingDifferentiable :
      DifferentiableAt ℝ responsePairing 0 :=
    responsePairingDerivative.differentiableAt
  have canonicalPairingDifferentiable :
      DifferentiableAt ℝ canonicalPairing 0 :=
    canonicalPairingDerivative.differentiableAt
  have responseMomentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe) =
        fun point => 2 * responsePairing point := by
    funext point
    exact quadraticResponse_probeMomentum_direction_one parameter point
  have canonicalMomentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe) =
        fun point => 2 * canonicalPairing point := by
    funext point
    exact canonicalResponse_probeMomentum_direction_one point
  rw [responseMomentumFunction, canonicalMomentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul responsePairingDifferentiable 2,
    fderiv_const_mul canonicalPairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative responsePairing 0 1 =
    2 * fieldDirectionalDerivative canonicalPairing 0 1
  rw [fieldDirectionalDerivative_pairing_const_local responseCurvature
      (fderiv ℝ responseCurvature 0) 0 1
      (p286CoordinateEquiv p286CommutatorProbeData)
      responseCurvatureDifferentiable.hasFDerivAt,
    fieldDirectionalDerivative_pairing_const_local canonicalCurvature
      (actualNativeCurvatureFDeriv 0) 0 1
      (p286CoordinateEquiv p286CommutatorProbeData)
      canonicalCurvatureDerivative]
  change
    2 * p286CoordinateLiePairing
        (fieldDirectionalDerivative
          (fun point =>
            colorCartanQuadraticResponseCurvatureCoordinate parameter point 0)
          0 1)
        (p286CoordinateEquiv p286CommutatorProbeData) =
      2 * p286CoordinateLiePairing
        (fieldDirectionalDerivative
          (fun point => actualNativeCurvatureCoordinate point 0) 0 1)
        (p286CoordinateEquiv p286CommutatorProbeData)
  have canonicalCurvatureFunctionEquality :
      (fun point =>
        holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0) =
      fun point => actualNativeCurvatureCoordinate point 0 := by
    rfl
  rw [colorCartanQuadraticResponseCurvature_pair_zero_direction_one,
    canonicalCurvatureFunctionEquality,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    colorCartanQuadraticCoordinate_pairing_commutatorProbe_eq_zero]
  ring

private theorem quadraticResponse_probeMomentum_direction_two_derivative
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe))
        0 2 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
      point 2 •
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 5
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    (holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 1).add
      (coordinateTwo_smul_contDiff _
        (holonomicGaugeCurvature_coordinate_contDiff
          (colorCartanQuadraticConstitutiveResponse parameter)
          (colorCartanQuadraticConstitutiveResponse_smooth parameter) 5))
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    (framedSmooth.differentiable (by simp)).differentiableAt
  have pairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact quadraticResponse_probeMomentum_direction_two parameter point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 2 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 2
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt,
    colorCartanQuadraticResponseFramedOne_direction_two_eq_zero]
  simp

private theorem canonicalResponse_probeMomentum_direction_two_derivative :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe))
        0 2 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    actualNativeCurvatureCoordinate point 1 +
      point 2 • actualNativeCurvatureCoordinate point 5
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have backgroundOneSmooth : ContDiff ℝ ∞ fun point =>
      actualNativeCurvatureCoordinate point 1 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 1
  have backgroundFiveSmooth : ContDiff ℝ ∞ fun point =>
      actualNativeCurvatureCoordinate point 5 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 5
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    backgroundOneSmooth.add
      (coordinateTwo_smul_contDiff _ backgroundFiveSmooth)
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    (framedSmooth.differentiable (by simp)).differentiableAt
  have pairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact canonicalResponse_probeMomentum_direction_two point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 2 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 2
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt,
    actualFramedCurvatureOne_direction_two_eq_zero]
  simp

private theorem quadraticResponse_probeMomentum_direction_three_derivative
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe))
        0 3 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
      point 2 •
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 4
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    (holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 2).sub
      (coordinateTwo_smul_contDiff _
        (holonomicGaugeCurvature_coordinate_contDiff
          (colorCartanQuadraticConstitutiveResponse parameter)
          (colorCartanQuadraticConstitutiveResponse_smooth parameter) 4))
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    (framedSmooth.differentiable (by simp)).differentiableAt
  have pairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact quadraticResponse_probeMomentum_direction_three parameter point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 3 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 3
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt,
    colorCartanQuadraticResponseFramedTwo_direction_three_eq_zero]
  simp

private theorem canonicalResponse_probeMomentum_direction_three_derivative :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe))
        0 3 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    actualNativeCurvatureCoordinate point 2 -
      point 2 • actualNativeCurvatureCoordinate point 4
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have backgroundTwoSmooth : ContDiff ℝ ∞ fun point =>
      actualNativeCurvatureCoordinate point 2 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 2
  have backgroundFourSmooth : ContDiff ℝ ∞ fun point =>
      actualNativeCurvatureCoordinate point 4 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 4
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    backgroundTwoSmooth.sub
      (coordinateTwo_smul_contDiff _ backgroundFourSmooth)
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    (framedSmooth.differentiable (by simp)).differentiableAt
  have pairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact canonicalResponse_probeMomentum_direction_three point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 3 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 3
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt,
    actualFramedCurvatureTwo_direction_three_eq_zero]
  simp

/-- Every member of the C3h78 quadratic color-Cartan family leaves the
commutator-probe BF divergence at its canonical value. -/
theorem colorCartanQuadraticConstitutiveResponse_probe_divergence_eq_one
    (parameter : ℝ) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (colorCartanQuadraticConstitutiveResponse parameter)
        p286CommutatorProbe 0 = 1 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [Fin.sum_univ_four,
    quadraticResponse_probeMomentum_direction_zero_derivative,
    quadraticResponse_probeMomentum_direction_one_derivative_eq_canonical,
    quadraticResponse_probeMomentum_direction_two_derivative,
    quadraticResponse_probeMomentum_direction_three_derivative]
  have canonicalDivergence :=
    canonicalSourceNativeP286Input_p286Divergence_probe_eq_one
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
    at canonicalDivergence
  rw [Fin.sum_univ_four,
    canonicalResponse_probeMomentum_direction_zero_derivative,
    canonicalResponse_probeMomentum_direction_two_derivative,
    canonicalResponse_probeMomentum_direction_three_derivative]
    at canonicalDivergence
  norm_num at canonicalDivergence ⊢
  exact canonicalDivergence

/-! ## Full probe residual and the stable negative gate -/

theorem colorCartanQuadraticConstitutiveResponse_algebraicCurrent_origin_eq_canonical
    (parameter : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (colorCartanQuadraticConstitutiveResponse parameter) direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource canonicalResponse direction 0 := by
  have algebraicDirectionEquality :
      p286GaugeConnectionAlgebraicCurvatureDirection
          (colorCartanQuadraticConstitutiveResponse parameter) direction 0 =
        p286GaugeConnectionAlgebraicCurvatureDirection canonicalResponse
          direction 0 := by
    funext pair
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    rw [colorCartanQuadraticConstitutiveResponse_connection_origin parameter]
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_pointField_origin parameter,
    algebraicDirectionEquality]
  rfl

/-- The independent commutator-probe residual is `-3` throughout the full
C3h78 coordinate family, including its residual-derived member. -/
theorem colorCartanQuadraticConstitutiveResponse_probe_EL_eq_neg_three
    (parameter : ℝ) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        (colorCartanQuadraticConstitutiveResponse parameter)
        p286CommutatorProbe 0 = -3 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_algebraicCurrent_origin_eq_canonical,
    colorCartanQuadraticConstitutiveResponse_probe_divergence_eq_one]
  have canonicalResidual :=
    canonicalSourceNativeP286Input_p286Residual_probe_eq_neg_three
  unfold p286GaugeConnectionEulerLagrangeCoefficient at canonicalResidual
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource canonicalResponse p286CommutatorProbe 0 -
        1 = -3
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource canonicalSourceNativeP286Input
          p286CommutatorProbe 0 -
        p286GaugeConnectionBFDifferentialMomentumDivergence
          canonicalSourceNativeP286Input p286CommutatorProbe 0 = -3
      at canonicalResidual
  rw [canonicalSourceNativeP286Input_p286Divergence_probe_eq_one]
    at canonicalResidual
  exact canonicalResidual

theorem colorCartanQuadraticResidualRepair_probe_EL_eq_neg_three :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource colorCartanQuadraticResidualRepair
        p286CommutatorProbe 0 = -3 :=
  colorCartanQuadraticConstitutiveResponse_probe_EL_eq_neg_three _

/-- Positive control: C3h78 cancels its selected color-Cartan projection,
but the independent commutator projection proves that it is not the full P286
pointwise solution. -/
theorem colorCartanQuadraticResidualRepair_not_fullP286Pointwise :
    ¬ CanonicalP286GaugeConnectionPointwiseEquation
        positiveSmoothUnifiedSource colorCartanQuadraticResidualRepair := by
  intro equation
  have probeFunctionZero := equation p286CommutatorProbe
  have probeOriginZero := congrFun probeFunctionZero 0
  rw [colorCartanQuadraticResidualRepair_probe_EL_eq_neg_three]
    at probeOriginZero
  norm_num at probeOriginZero

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorCartanQuadraticResidualSupportBoundary
