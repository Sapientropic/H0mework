import H0mework.Physics.GaugeAction.P286SameLineageAffineResponseSpecialization
import H0mework.Physics.Matter.P286ColorMixingOriginResidualTransport

/-!
# S9-C3h77c infrastructure: actual P286 source-affine curvature-jet normal form

This module computes the actual source-affine P286 connection coordinates,
the curvature first derivative at the canonical origin, and the constitutive
BF differential-momentum normal form used by the color-Cartan audit.  The
auxiliary field is read from the canonical source-native constitutive jet; it
is not replaced by the residual-limit constant auxiliary.

This is analytic readout infrastructure.  It does not choose a connection
shift, classify a response range or zero fiber, produce stationarity, add a
source receipt, or introduce a new dynamical or constitutive field.  The fixed
color-Cartan direction and its four-sector offset are owned by the downstream
boundary module.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286SourceAffineCurvatureJetNormalForm

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCompactSupportIntegrationByParts
open StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineGravityAlgebraicKeepResponseP286Defect
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286FixedBackgroundAffineResponseFiber
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286SameLineageAffineResponseSpecialization
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286BFBalanceDecision
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Actual auxiliary jet and its source-affine curvature -/

def actualNativeCurvatureCoordinate (point : BasePoint) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv
    (holonomicGaugeCurvature
      (positiveSourceNativeKinematicSeed residualLimitLorentzCarrierReader)
      point pair)

def actualSourceAffineCoordinate
    (formDirection : LorentzianIndex) (point : BasePoint) :
    P286CoordinateCarrier :=
  sourceP286AffineConnectionCoordinate positiveSmoothUnifiedSource.legacy
    point formDirection

def actualSourceAffineIncrement
    (formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
    formDirection

def actualSourceAffineExteriorZero : P286LieBlockData :=
  sourceP286ExteriorDerivative positiveSmoothUnifiedSource.legacy 0

theorem positiveSourceP286Potential_zero_coordinate_local :
    p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 0) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorCartanP286ConnectionDirection := by
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        colorCartanP286ConnectionDirection) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

theorem positiveSourceP286Potential_one_coordinate_local :
    p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 1) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorMixingP286ConnectionDirection := by
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        colorMixingP286ConnectionDirection) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

theorem p286CommutatorData_eq_mixing_cartan_local :
    p286CommutatorProbeData =
      p286LieBracket colorMixingP286ConnectionDirection
        colorCartanP286ConnectionDirection := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;>
      simp [p286CommutatorProbeData, canonicalP286Generator,
        colorMixingP286ConnectionDirection,
        colorCartanP286ConnectionDirection, p286LieBracket, suLieBracket]

theorem actualSourceAffineExteriorZero_coordinate_normalForm :
    p286CoordinateEquiv actualSourceAffineExteriorZero =
      (1 / 4 : ℝ) • p286CoordinateEquiv canonicalP286Generator +
        (1 / 4 : ℝ) • p286CoordinateEquiv p286CommutatorProbeData := by
  unfold actualSourceAffineExteriorZero sourceP286ExteriorDerivative
  rw [map_sub, positiveSourceP286TargetCurvature_apply]
  simp only [if_pos, pairFirst, pairSecond, Matrix.cons_val_zero]
  rw [← p286CoordinateLieBracket_equiv_apply,
    positiveSourceP286Potential_zero_coordinate_local,
    positiveSourceP286Potential_one_coordinate_local,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_equiv_apply,
    p286CommutatorData_eq_mixing_cartan_local]
  have antisymmetry :
      p286LieBracket colorCartanP286ConnectionDirection
          colorMixingP286ConnectionDirection =
        -p286LieBracket colorMixingP286ConnectionDirection
          colorCartanP286ConnectionDirection := by
    apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · apply Prod.ext
      · apply Subtype.ext
        simp [p286LieBracket, suLieBracket]
      · simp [p286LieBracket]
  rw [antisymmetry, map_neg]
  module

theorem actualNativeAuxiliaryCoordinate_eq_constitutive
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input point =
      p286GaugeConstitutiveAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        (canonicalPhysicalSource.coframeAt point)
        (actualNativeCurvatureCoordinate point) := by
  funext pair
  simp only [holonomicP286GaugeAuxiliaryCoordinate,
    canonicalSourceNativeP286Input,
    positiveSourceNativeAlgebraicEliminationUpdate,
    generatedP286GaugeConstitutiveAuxiliary,
    p286CoordinateEquiv.apply_symm_apply]
  rfl

theorem p286CoordinateLiePairing_neg_left_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing (-first) second =
      -p286CoordinateLiePairing first second := by
  rw [show -first = (-1 : ℝ) • first by simp,
    p286CoordinateLiePairing_smul_left]
  ring

theorem p286CoordinateLiePairing_neg_right_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

theorem specialUnitaryLiePairing_bracket_left_local
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (suLieBracket first second) residual =
      specialUnitaryLiePairing first (suLieBracket second residual) := by
  unfold specialUnitaryLiePairing suLieBracket
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle'
    (first : Matrix n n ℂ) (residual : Matrix n n ℂ)
    (second : Matrix n n ℂ)]

theorem p286LiePairing_bracket_left_local
    (first second residual : P286LieBlockData) :
    p286LiePairing (p286LieBracket first second) residual =
      p286LiePairing first (p286LieBracket second residual) := by
  unfold p286LiePairing p286LieBracket
  rw [specialUnitaryLiePairing_bracket_left_local,
    specialUnitaryLiePairing_bracket_left_local]
  simp [hyperchargeLiePairing]

theorem p286CoordinateLiePairing_bracket_left_local
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket first second) residual =
      p286CoordinateLiePairing first
        (p286CoordinateLieBracket second residual) := by
  unfold p286CoordinateLiePairing p286CoordinateLieBracket
  simp only [LinearEquiv.symm_apply_apply]
  exact p286LiePairing_bracket_left_local _ _ _

theorem p286CommutatorData_pairing_self_eq_eight_local :
    p286CoordinateLiePairing
        (p286CoordinateEquiv p286CommutatorProbeData)
        (p286CoordinateEquiv p286CommutatorProbeData) = 8 := by
  rw [p286CommutatorData_eq_mixing_cartan_local]
  calc
    p286CoordinateLiePairing
        (p286CoordinateEquiv
          (p286LieBracket colorMixingP286ConnectionDirection
            colorCartanP286ConnectionDirection))
        (p286CoordinateEquiv
          (p286LieBracket colorMixingP286ConnectionDirection
            colorCartanP286ConnectionDirection)) =
      p286CoordinateLiePairing
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorMixingP286ConnectionDirection)
          (p286CoordinateEquiv colorCartanP286ConnectionDirection))
        (p286CoordinateEquiv
          (p286LieBracket colorMixingP286ConnectionDirection
            colorCartanP286ConnectionDirection)) := by
          rw [p286CoordinateLieBracket_equiv_apply]
    _ = p286CoordinateLiePairing
        (p286CoordinateEquiv colorMixingP286ConnectionDirection)
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorCartanP286ConnectionDirection)
          (p286CoordinateEquiv
            (p286LieBracket colorMixingP286ConnectionDirection
              colorCartanP286ConnectionDirection))) := by
          rw [p286CoordinateLiePairing_bracket_left_local]
    _ = p286CoordinateLiePairing
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorCartanP286ConnectionDirection)
          (p286CoordinateEquiv
            (p286LieBracket colorMixingP286ConnectionDirection
              colorCartanP286ConnectionDirection)))
        (p286CoordinateEquiv colorMixingP286ConnectionDirection) := by
          rw [p286CoordinateLiePairing_symmetric]
    _ = p286CoordinateLiePairing
        (p286CoordinateEquiv colorCartanP286ConnectionDirection)
        (p286CoordinateLieBracket
          (p286CoordinateEquiv
            (p286LieBracket colorMixingP286ConnectionDirection
              colorCartanP286ConnectionDirection))
          (p286CoordinateEquiv colorMixingP286ConnectionDirection)) := by
          rw [p286CoordinateLiePairing_bracket_left_local]
    _ = p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateEquiv p286DoubleCommutatorProbeData) := by
          rw [p286CoordinateLieBracket_equiv_apply]
          unfold p286CoordinateLiePairing
          simp only [p286CoordinateEquiv.symm_apply_apply]
          unfold p286LiePairing
          simp [colorCartanP286ConnectionDirection,
            colorMixingP286ConnectionDirection, canonicalP286Generator,
            p286DoubleCommutatorProbeData,
            p286CommutatorData_eq_mixing_cartan_local, p286LieBracket,
            specialUnitaryLiePairing, hyperchargeLiePairing]
    _ = 8 := p286ProbePairing_eq_eight

theorem p286LieBracket_antisymm_local
    (first second : P286LieBlockData) :
    p286LieBracket first second = -p286LieBracket second first := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

theorem p286LieBracket_zero_right_local
    (first : P286LieBlockData) :
    p286LieBracket first 0 = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

theorem p286LieBracket_zero_left_local
    (second : P286LieBlockData) :
    p286LieBracket 0 second = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

theorem p286CoordinateLieBracket_antisymm_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket first second =
      -p286CoordinateLieBracket second first := by
  unfold p286CoordinateLieBracket
  rw [p286LieBracket_antisymm_local, map_neg]

theorem p286CoordinateLieBracket_zero_right_local
    (first : P286CoordinateCarrier) :
    p286CoordinateLieBracket first 0 = 0 := by
  unfold p286CoordinateLieBracket
  rw [map_zero, p286LieBracket_zero_right_local, map_zero]

theorem p286CoordinateLieBracket_zero_left_local
    (second : P286CoordinateCarrier) :
    p286CoordinateLieBracket 0 second = 0 := by
  unfold p286CoordinateLieBracket
  rw [map_zero, p286LieBracket_zero_left_local, map_zero]

theorem canonicalP286Pairing_commutatorData_eq_zero_local :
    p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateEquiv p286CommutatorProbeData) = 0 := by
  rw [p286CommutatorData_eq_mixing_cartan_local]
  rw [← p286CoordinateLieBracket_equiv_apply,
    p286CoordinateLieBracket_antisymm_local,
    p286CoordinateLiePairing_neg_right_local,
    canonicalP286Pairing_colorCartanBracket_zero]
  norm_num

theorem actualSourceAffineExteriorZero_pairing_commutator_eq_two :
    p286CoordinateLiePairing
        (p286CoordinateEquiv actualSourceAffineExteriorZero)
        (p286CoordinateEquiv p286CommutatorProbeData) = 2 := by
  rw [actualSourceAffineExteriorZero_coordinate_normalForm,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    canonicalP286Pairing_commutatorData_eq_zero_local,
    p286CommutatorData_pairing_self_eq_eight_local]
  norm_num

theorem actualExterior_mixing_pairing_colorCartan_eq_two :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket
          (p286CoordinateEquiv actualSourceAffineExteriorZero)
          (p286CoordinateEquiv colorMixingP286ConnectionDirection))
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) = 2 := by
  rw [p286CoordinateLiePairing_bracket_left_local,
    p286CoordinateLieBracket_equiv_apply,
    ← p286CommutatorData_eq_mixing_cartan_local,
    actualSourceAffineExteriorZero_pairing_commutator_eq_two]

/-! ## Constitutive momentum normal form -/

theorem liftGaugeTwoFormOperator_fixedHodge_apply_local
    (form : P286GaugeTwoForm) (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge form pair =
      ![form 3, form 4, form 5, -form 0, -form 1, -form 2] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> rfl

theorem p286FixedHodge_pairing_pairing_local
    (first second : P286GaugeTwoForm) :
    (∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        p286CoordinateLiePairing
          (liftGaugeTwoFormOperator lorentzianCoframeHodge first pair)
          (liftGaugeTwoFormOperator lorentzianCoframeHodge second pair)) =
      -(∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing (first pair) (second pair)) := by
  rw [Fin.sum_univ_six, Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_fixedHodge_apply_local]
  simp [lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_left_local,
    p286CoordinateLiePairing_neg_right_local]
  ring

theorem liftGaugeTwoFormOperator_positiveSourceFrame_apply_local
    (form : P286GaugeTwoForm) (point : BasePoint) (pair : Fin 6) :
    liftGaugeTwoFormOperator
        (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
        form pair =
      ![form 0,
        form 1 + point 2 • form 5,
        form 2 - point 2 • form 4,
        form 3, form 4, form 5] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply,
    coframeTwoFormLinear_positiveSource]
  fin_cases pair <;>
    simp [positiveCoframeTwoFormFrame, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val]

theorem canonicalInput_p286DifferentialMomentum_normalForm_local
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        direction point =
      2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
              (actualNativeCurvatureCoordinate point) pair)
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
              direction pair) := by
  unfold p286GaugeConnectionBFDifferentialMomentum
  change
    abs (Matrix.det (canonicalSourceNativeP286Input.coframe point)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (canonicalSourceNativeP286Input.coframe point)
          (holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input
            point)
          direction = _
  rw [show canonicalSourceNativeP286Input.coframe point =
    canonicalPhysicalSource.coframeAt point by rfl,
    actualNativeAuxiliaryCoordinate_eq_constitutive,
    canonicalPhysicalSource_coframeAt_det]
  simp only [abs_one, one_mul]
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  have couplingInverse :
      (((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)⁻¹) = 2 := by
    change (positiveSmoothUnifiedSource.legacy.sigma)⁻¹ = 2
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
    norm_num
  rw [couplingInverse]
  simp_rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [liftCoframe_dynamicHodge_p286
    (canonicalPhysicalSource.coframeAt point)
    (canonicalPhysicalSource_globally_nondegenerate point)
    (actualNativeCurvatureCoordinate point)]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  let framedCurvature :=
    liftGaugeTwoFormOperator
      (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
      (actualNativeCurvatureCoordinate point)
  let framedDirection :=
    liftGaugeTwoFormOperator
      (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
      direction
  calc
    (∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        (-2 * p286CoordinateLiePairing
          (liftGaugeTwoFormOperator lorentzianCoframeHodge
            framedCurvature pair)
          (liftGaugeTwoFormOperator lorentzianCoframeHodge
            framedDirection pair))) =
      -2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator lorentzianCoframeHodge
              framedCurvature pair)
            (liftGaugeTwoFormOperator lorentzianCoframeHodge
              framedDirection pair) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pair _
        ring
    _ = 2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing (framedCurvature pair)
            (framedDirection pair) := by
      rw [p286FixedHodge_pairing_pairing_local]
      ring
    _ = _ := rfl

/-! ## Source-affine curvature jet at the origin -/

theorem actualSourceAffineCoordinate_hasFDerivAt
    (formDirection : LorentzianIndex) (point : BasePoint) :
    HasFDerivAt (actualSourceAffineCoordinate formDirection)
      (actualSourceAffineIncrement formDirection) point := by
  change HasFDerivAt
    (fun point =>
      p286CoordinateEquiv
          (sourceP286Potential positiveSmoothUnifiedSource.legacy
            formDirection) +
        sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
          formDirection point)
    (sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
      formDirection) point
  exact (sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
    formDirection).hasFDerivAt.const_add _

theorem actualSourceAffineIncrement_coordinateDirection
    (formDirection derivativeDirection : LorentzianIndex) :
    actualSourceAffineIncrement formDirection
        (coordinateDirection derivativeDirection) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv
          (sourceP286ExteriorDerivativeComponent
            positiveSmoothUnifiedSource.legacy
            derivativeDirection formDirection) := by
  simp only [actualSourceAffineIncrement, sourceP286AffineIncrementLinear]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [coordinateDirection, Fin.sum_univ_four]

theorem actualSourceAffineCoordinate_origin
    (formDirection : LorentzianIndex) :
    actualSourceAffineCoordinate formDirection 0 =
      p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy
          formDirection) := by
  simp [actualSourceAffineCoordinate, sourceP286AffineConnectionCoordinate]

theorem actualNativeP286ConnectionDerivative_coordinate
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286CoordinateEquiv
        (p286ConnectionDerivative
          (positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader)
          point derivativeDirection formDirection) =
      actualSourceAffineIncrement formDirection
        (coordinateDirection derivativeDirection) := by
  unfold p286ConnectionDerivative
  simp only [p286CoordinateEquiv.apply_symm_apply]
  have connectionCoordinate :
      (fun candidate =>
        p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection
              candidate formDirection)) =
        actualSourceAffineCoordinate formDirection := by
    funext candidate
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, actualSourceAffineCoordinate]
  rw [connectionCoordinate]
  unfold fieldDirectionalDerivative
  rw [(actualSourceAffineCoordinate_hasFDerivAt formDirection point).fderiv]

theorem actualSourceAffineBracket_directionalDerivative_origin
    (first second derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => p286CoordinateLieBracket
          (actualSourceAffineCoordinate first point)
          (actualSourceAffineCoordinate second point))
        0 derivativeDirection =
      p286CoordinateLieBracket
          (actualSourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (actualSourceAffineCoordinate second 0) +
        p286CoordinateLieBracket
          (actualSourceAffineCoordinate first 0)
          (actualSourceAffineIncrement second
            (coordinateDirection derivativeDirection)) := by
  have derivative :=
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (actualSourceAffineCoordinate_hasFDerivAt first 0)
        (actualSourceAffineCoordinate_hasFDerivAt second 0)).fderiv
  have evaluated := congrArg
    (fun linear : BasePoint →L[ℝ] P286CoordinateCarrier =>
      linear (coordinateDirection derivativeDirection)) derivative
  change
    (fderiv ℝ
      (fun point => p286CoordinateLieBracket
        (actualSourceAffineCoordinate first point)
        (actualSourceAffineCoordinate second point)) 0)
        (coordinateDirection derivativeDirection) =
      p286CoordinateLieBracket (actualSourceAffineCoordinate first 0)
          (actualSourceAffineIncrement second
            (coordinateDirection derivativeDirection)) +
        p286CoordinateLieBracket
          (actualSourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (actualSourceAffineCoordinate second 0) at evaluated
  unfold fieldDirectionalDerivative
  change fderiv ℝ
    (fun point => p286CoordinateLieBracket
      (actualSourceAffineCoordinate first point)
      (actualSourceAffineCoordinate second point)) 0
      (coordinateDirection derivativeDirection) = _
  calc
    _ = p286CoordinateLieBracket
          (actualSourceAffineCoordinate first 0)
          (actualSourceAffineIncrement second
            (coordinateDirection derivativeDirection)) +
        p286CoordinateLieBracket
          (actualSourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (actualSourceAffineCoordinate second 0) := by
      exact evaluated
    _ = _ := add_comm _ _

theorem actualNativeCurvatureCoordinate_normalForm
    (point : BasePoint) (pair : Fin 6) :
    actualNativeCurvatureCoordinate point pair =
      p286CoordinateEquiv
          (sourceP286ExteriorDerivative
            positiveSmoothUnifiedSource.legacy pair) +
        p286CoordinateLieBracket
          (actualSourceAffineCoordinate (pairFirst pair) point)
          (actualSourceAffineCoordinate (pairSecond pair) point) := by
  unfold actualNativeCurvatureCoordinate holonomicGaugeCurvature
  rw [map_add, map_sub,
    actualNativeP286ConnectionDerivative_coordinate,
    actualNativeP286ConnectionDerivative_coordinate,
    actualSourceAffineIncrement_coordinateDirection,
    actualSourceAffineIncrement_coordinateDirection,
    sourceP286ExteriorDerivativeComponent_antisymm
      positiveSmoothUnifiedSource.legacy (pairSecond pair) (pairFirst pair),
    sourceP286ExteriorDerivativeComponent_pair]
  simp only [map_neg]
  have firstCoordinate :
      p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection point
              (pairFirst pair)) =
        actualSourceAffineCoordinate (pairFirst pair) point := by
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, actualSourceAffineCoordinate]
  have secondCoordinate :
      p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection point
              (pairSecond pair)) =
        actualSourceAffineCoordinate (pairSecond pair) point := by
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, actualSourceAffineCoordinate]
  have firstData :
      (positiveSourceNativeKinematicSeed
        residualLimitLorentzCarrierReader).gaugeConnection point
          (pairFirst pair) =
        p286CoordinateEquiv.symm
          (actualSourceAffineCoordinate (pairFirst pair) point) := by
    apply p286CoordinateEquiv.injective
    rw [firstCoordinate, p286CoordinateEquiv.apply_symm_apply]
  have secondData :
      (positiveSourceNativeKinematicSeed
        residualLimitLorentzCarrierReader).gaugeConnection point
          (pairSecond pair) =
        p286CoordinateEquiv.symm
          (actualSourceAffineCoordinate (pairSecond pair) point) := by
    apply p286CoordinateEquiv.injective
    rw [secondCoordinate, p286CoordinateEquiv.apply_symm_apply]
  rw [show p286CoordinateEquiv
      (p286LieBracket
        ((positiveSourceNativeKinematicSeed
          residualLimitLorentzCarrierReader).gaugeConnection point
            (pairFirst pair))
        ((positiveSourceNativeKinematicSeed
          residualLimitLorentzCarrierReader).gaugeConnection point
            (pairSecond pair))) =
      p286CoordinateLieBracket
        (actualSourceAffineCoordinate (pairFirst pair) point)
        (actualSourceAffineCoordinate (pairSecond pair) point) by
    unfold p286CoordinateLieBracket
    rw [firstData, secondData]]
  module

theorem actualNativeCurvatureCoordinate_directionalDerivative_origin
    (pair : Fin 6) (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => actualNativeCurvatureCoordinate point pair)
        0 derivativeDirection =
      p286CoordinateLieBracket
          (actualSourceAffineIncrement (pairFirst pair)
            (coordinateDirection derivativeDirection))
          (actualSourceAffineCoordinate (pairSecond pair) 0) +
        p286CoordinateLieBracket
          (actualSourceAffineCoordinate (pairFirst pair) 0)
          (actualSourceAffineIncrement (pairSecond pair)
            (coordinateDirection derivativeDirection)) := by
  have curvatureFunction :
      (fun point => actualNativeCurvatureCoordinate point pair) =
        fun point =>
          p286CoordinateEquiv
              (sourceP286ExteriorDerivative
                positiveSmoothUnifiedSource.legacy pair) +
            p286CoordinateLieBracket
              (actualSourceAffineCoordinate (pairFirst pair) point)
              (actualSourceAffineCoordinate (pairSecond pair) point) := by
    funext point
    exact actualNativeCurvatureCoordinate_normalForm point pair
  have bracketDerivative :=
    actualSourceAffineBracket_directionalDerivative_origin
      (pairFirst pair) (pairSecond pair) derivativeDirection
  unfold fieldDirectionalDerivative at bracketDerivative ⊢
  rw [curvatureFunction, fderiv_const_add]
  exact bracketDerivative

def actualNativeCurvatureFDeriv
    (pair : Fin 6) : BasePoint →L[ℝ] P286CoordinateCarrier :=
  (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.precompR
      BasePoint (actualSourceAffineCoordinate (pairFirst pair) 0)
      (actualSourceAffineIncrement (pairSecond pair))) +
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.precompL
      BasePoint (actualSourceAffineIncrement (pairFirst pair))
      (actualSourceAffineCoordinate (pairSecond pair) 0))

theorem actualNativeCurvatureCoordinate_hasFDerivAt_origin
    (pair : Fin 6) :
    HasFDerivAt (fun point => actualNativeCurvatureCoordinate point pair)
      (actualNativeCurvatureFDeriv pair) 0 := by
  have bracketDerivative :=
    p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (actualSourceAffineCoordinate_hasFDerivAt (pairFirst pair) 0)
        (actualSourceAffineCoordinate_hasFDerivAt (pairSecond pair) 0)
  have withConstant := bracketDerivative.const_add
    (p286CoordinateEquiv
      (sourceP286ExteriorDerivative positiveSmoothUnifiedSource.legacy pair))
  have functionEquality :
      (fun point => actualNativeCurvatureCoordinate point pair) =
        fun point =>
          p286CoordinateEquiv
              (sourceP286ExteriorDerivative
                positiveSmoothUnifiedSource.legacy pair) +
            p286CoordinateLieBracket
              (actualSourceAffineCoordinate (pairFirst pair) point)
              (actualSourceAffineCoordinate (pairSecond pair) point) := by
    funext point
    exact actualNativeCurvatureCoordinate_normalForm point pair
  rw [functionEquality]
  exact withConstant

theorem fieldDirectionalDerivative_pairing_const_local
    (field : BasePoint → P286CoordinateCarrier)
    (fieldDerivative : BasePoint →L[ℝ] P286CoordinateCarrier)
    (point : BasePoint) (derivativeDirection : LorentzianIndex)
    (residual : P286CoordinateCarrier)
    (hasDerivative : HasFDerivAt field fieldDerivative point) :
    fieldDirectionalDerivative
        (fun candidate => p286CoordinateLiePairing
          (field candidate) residual) point derivativeDirection =
      p286CoordinateLiePairing
        (fieldDirectionalDerivative field point derivativeDirection)
        residual := by
  have pairingDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear hasDerivative
        (hasFDerivAt_const residual point)
  have derivativeEquality := pairingDerivative.fderiv
  have evaluated := congrArg
    (fun linear : BasePoint →L[ℝ] ℝ =>
      linear (coordinateDirection derivativeDirection)) derivativeEquality
  simp only [map_zero, zero_add] at evaluated
  change
    (fderiv ℝ
      (fun candidate =>
        p286CoordinateLiePairingBilinear.toContinuousBilinearMap
          (field candidate) residual) point)
        (coordinateDirection derivativeDirection) =
      p286CoordinateLiePairing
        (fieldDerivative (coordinateDirection derivativeDirection)) residual
    at evaluated
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun candidate => p286CoordinateLiePairing
        (field candidate) residual) point)
        (coordinateDirection derivativeDirection) = _
  change
    (fderiv ℝ
      (fun candidate =>
        p286CoordinateLiePairingBilinear.toContinuousBilinearMap
          (field candidate) residual) point)
        (coordinateDirection derivativeDirection) = _
  rw [hasDerivative.fderiv]
  exact evaluated

theorem actualSourceAffineIncrement_zero_direction_one :
    actualSourceAffineIncrement 0 (coordinateDirection 1) =
      -(1 / 2 : ℝ) • p286CoordinateEquiv actualSourceAffineExteriorZero := by
  rw [actualSourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent,
    actualSourceAffineExteriorZero]

theorem actualSourceAffineIncrement_one_direction_one :
    actualSourceAffineIncrement 1 (coordinateDirection 1) = 0 := by
  rw [actualSourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

theorem actualSourceAffineCoordinate_zero_origin :
    actualSourceAffineCoordinate 0 0 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorCartanP286ConnectionDirection := by
  rw [actualSourceAffineCoordinate_origin,
    positiveSourceP286Potential_zero_coordinate_local]

theorem actualSourceAffineCoordinate_one_origin :
    actualSourceAffineCoordinate 1 0 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorMixingP286ConnectionDirection := by
  rw [actualSourceAffineCoordinate_origin,
    positiveSourceP286Potential_one_coordinate_local]

theorem actualNativeCurvature_zero_direction_one_pairing_colorCartan_eq_neg_half :
    p286CoordinateLiePairing
        (fieldDirectionalDerivative
          (fun point => actualNativeCurvatureCoordinate point 0) 0 1)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) =
      -(1 / 2 : ℝ) := by
  rw [actualNativeCurvatureCoordinate_directionalDerivative_origin]
  simp only [pairFirst, pairSecond, Matrix.cons_val_zero]
  rw [actualSourceAffineIncrement_zero_direction_one,
    actualSourceAffineIncrement_one_direction_one,
    actualSourceAffineCoordinate_one_origin,
    p286CoordinateLieBracket_zero_right_local,
    add_zero,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    actualExterior_mixing_pairing_colorCartan_eq_two]
  norm_num

theorem actualSourceAffineCoordinate_two_origin :
    actualSourceAffineCoordinate 2 0 = 0 := by
  rw [actualSourceAffineCoordinate_origin]
  simp [sourceP286Potential]

theorem actualSourceAffineCoordinate_three_origin :
    actualSourceAffineCoordinate 3 0 = 0 := by
  rw [actualSourceAffineCoordinate_origin]
  simp [sourceP286Potential]

theorem actualSourceAffineIncrement_two_direction_two :
    actualSourceAffineIncrement 2 (coordinateDirection 2) = 0 := by
  rw [actualSourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

theorem actualSourceAffineIncrement_three_direction_three :
    actualSourceAffineIncrement 3 (coordinateDirection 3) = 0 := by
  rw [actualSourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

theorem actualNativeCurvature_one_direction_two_eq_zero :
    fieldDirectionalDerivative
        (fun point => actualNativeCurvatureCoordinate point 1) 0 2 = 0 := by
  rw [actualNativeCurvatureCoordinate_directionalDerivative_origin]
  simp only [pairFirst, pairSecond, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [actualSourceAffineCoordinate_two_origin,
    actualSourceAffineIncrement_two_direction_two]
  simp

theorem actualNativeCurvature_two_direction_three_eq_zero :
    fieldDirectionalDerivative
        (fun point => actualNativeCurvatureCoordinate point 2) 0 3 = 0 := by
  rw [actualNativeCurvatureCoordinate_directionalDerivative_origin]
  change
    p286CoordinateLieBracket
        (actualSourceAffineIncrement 0 (coordinateDirection 3))
        (actualSourceAffineCoordinate 3 0) +
      p286CoordinateLieBracket (actualSourceAffineCoordinate 0 0)
        (actualSourceAffineIncrement 3 (coordinateDirection 3)) = 0
  rw [actualSourceAffineCoordinate_three_origin,
    actualSourceAffineIncrement_three_direction_three]
  simp

theorem actualNativeCurvatureCoordinate_origin
    (pair : Fin 6) :
    actualNativeCurvatureCoordinate 0 pair =
      p286CoordinateEquiv
        (sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy pair) := by
  unfold actualNativeCurvatureCoordinate
  rw [show positiveSourceNativeKinematicSeed
      residualLimitLorentzCarrierReader =
      installSourceP286AffineConnection positiveSmoothUnifiedSource.legacy
        (installPositiveSourceNativeGravityKinematics
          residualLimitLorentzCarrierReader) by rfl]
  rw [holonomicGaugeCurvature_installSourceP286AffineConnection_origin]

theorem actualNativeCurvatureCoordinate_origin_five_eq_zero :
    actualNativeCurvatureCoordinate 0 5 = 0 := by
  rw [actualNativeCurvatureCoordinate_origin,
    positiveSourceP286TargetCurvature_apply]
  split_ifs with h
  · omega
  · rfl

end

end SaturationMonoid.PhysicsCore.StageNineP286SourceAffineCurvatureJetNormalForm
