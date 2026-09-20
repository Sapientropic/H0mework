import H0mework.Physics.GravityResponse.FullDefect
import H0mework.Physics.Matter.P286ColorMixingOriginResidualTransport
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# S9-C3h72d: actual P286 responsibility of the gravity keep response

This diagnostic computes the P286 connection Euler--Lagrange residual of the
actual-curvature algebraic eliminator.  The gauge auxiliary is always the
constitutive inverse of the varying `dA + [A,A]` curvature; it is never
replaced by the older constant-target-curvature reference auxiliary.

For the canonical source-native input, the four divergence directions are
`(0,1,0,0)`, so the actual divergence is `1`.  Together with BF algebraic
value `-2` and zero scalar/matter currents, the P286 residual is `-3`.
Source `sigma=1/2` then makes both the input trace and C3h70 lift defect
`-3/2`.  These are action-derived readouts, not supplied residual values,
zero-fiber witnesses, branches, or stationarity receipts.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseP286Defect

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseFullDefect
open StageNineGravityAlgebraicKeepResponseGerm
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286BFBalanceDecision
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineSourceGeneratedP286AffineConnectionGerm
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

abbrev canonicalSourceNativeP286Input : StageNineHolonomicConfiguration :=
  positiveSourceNativeAlgebraicEliminationUpdate
    residualLimitLorentzCarrierReader

abbrev canonicalSourceNativeP286Response : StageNineHolonomicConfiguration :=
  positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate canonicalSourceNativeP286Input

private def nativeCurvatureCoordinate (point : BasePoint) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv
    (holonomicGaugeCurvature
      (positiveSourceNativeKinematicSeed residualLimitLorentzCarrierReader)
      point pair)

private def sourceAffineCoordinate
    (formDirection : LorentzianIndex) (point : BasePoint) :
    P286CoordinateCarrier :=
  sourceP286AffineConnectionCoordinate positiveSmoothUnifiedSource.legacy
    point formDirection

private def sourceAffineIncrement
    (formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
    formDirection

private def sourceAffineExteriorZero : P286LieBlockData :=
  sourceP286ExteriorDerivative positiveSmoothUnifiedSource.legacy 0

private theorem positiveSourceP286Potential_zero_coordinate :
    p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 0) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorCartanP286ConnectionDirection := by
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        colorCartanP286ConnectionDirection) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

private theorem positiveSourceP286Potential_one_coordinate :
    p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy 1) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorMixingP286ConnectionDirection := by
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        colorMixingP286ConnectionDirection) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

private theorem p286CommutatorProbeData_eq_mixing_cartan :
    p286CommutatorProbeData =
      p286LieBracket colorMixingP286ConnectionDirection
        colorCartanP286ConnectionDirection := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;>
      simp [p286CommutatorProbeData, canonicalP286Generator,
        colorMixingP286ConnectionDirection,
        colorCartanP286ConnectionDirection, p286LieBracket, suLieBracket]

private theorem sourceAffineExteriorZero_coordinate_normalForm :
    p286CoordinateEquiv sourceAffineExteriorZero =
      (1 / 4 : ℝ) • p286CoordinateEquiv canonicalP286Generator +
        (1 / 4 : ℝ) • p286CoordinateEquiv p286CommutatorProbeData := by
  unfold sourceAffineExteriorZero sourceP286ExteriorDerivative
  rw [map_sub, positiveSourceP286TargetCurvature_apply]
  simp only [if_pos, pairFirst, pairSecond, Matrix.cons_val_zero]
  rw [← p286CoordinateLieBracket_equiv_apply,
    positiveSourceP286Potential_zero_coordinate,
    positiveSourceP286Potential_one_coordinate,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_equiv_apply,
    p286CommutatorProbeData_eq_mixing_cartan]
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

private theorem nativeAuxiliaryCoordinate_eq_constitutive
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input point =
      p286GaugeConstitutiveAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        (canonicalPhysicalSource.coframeAt point)
        (nativeCurvatureCoordinate point) := by
  funext pair
  simp only [holonomicP286GaugeAuxiliaryCoordinate, canonicalSourceNativeP286Input,
    positiveSourceNativeAlgebraicEliminationUpdate,
    generatedP286GaugeConstitutiveAuxiliary,
    p286CoordinateEquiv.apply_symm_apply]
  rfl

private theorem p286CoordinateLiePairing_neg_left
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing (-first) second =
      -p286CoordinateLiePairing first second := by
  rw [show -first = (-1 : ℝ) • first by simp,
    p286CoordinateLiePairing_smul_left]
  ring

private theorem p286CoordinateLiePairing_neg_right
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

private theorem specialUnitaryLiePairing_bracket_left
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

private theorem p286LiePairing_bracket_left
    (first second residual : P286LieBlockData) :
    p286LiePairing (p286LieBracket first second) residual =
      p286LiePairing first (p286LieBracket second residual) := by
  unfold p286LiePairing p286LieBracket
  rw [specialUnitaryLiePairing_bracket_left,
    specialUnitaryLiePairing_bracket_left]
  simp [hyperchargeLiePairing]

private theorem p286CoordinateLiePairing_bracket_left
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket first second) residual =
      p286CoordinateLiePairing first
        (p286CoordinateLieBracket second residual) := by
  unfold p286CoordinateLiePairing p286CoordinateLieBracket
  simp only [LinearEquiv.symm_apply_apply]
  exact p286LiePairing_bracket_left _ _ _

private theorem p286LiePairing_self_bracket_zero
    (matrix residual : P286LieBlockData) :
    p286LiePairing matrix (p286LieBracket matrix residual) = 0 := by
  unfold p286LiePairing p286LieBracket
  rw [specialUnitaryLiePairing_self_bracket_zero,
    specialUnitaryLiePairing_self_bracket_zero]
  simp [hyperchargeLiePairing]

private theorem p286CommutatorProbeData_pairing_self_eq_eight :
    p286CoordinateLiePairing
        (p286CoordinateEquiv p286CommutatorProbeData)
        (p286CoordinateEquiv p286CommutatorProbeData) = 8 := by
  rw [p286CommutatorProbeData_eq_mixing_cartan]
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
          rw [p286CoordinateLiePairing_bracket_left]
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
          rw [p286CoordinateLiePairing_bracket_left]
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
            p286CommutatorProbeData_eq_mixing_cartan, p286LieBracket,
            specialUnitaryLiePairing, hyperchargeLiePairing]
    _ = 8 := p286ProbePairing_eq_eight

private theorem p286DoubleCommutator_pairing_commutator_eq_zero :
    p286CoordinateLiePairing
        (p286CoordinateEquiv p286DoubleCommutatorProbeData)
        (p286CoordinateEquiv p286CommutatorProbeData) = 0 := by
  rw [p286CoordinateLiePairing_symmetric]
  unfold p286DoubleCommutatorProbeData
  simp only [p286CoordinateLiePairing,
    p286CoordinateEquiv.symm_apply_apply]
  exact p286LiePairing_self_bracket_zero _ _

private theorem p286LieBracket_antisymm
    (first second : P286LieBlockData) :
    p286LieBracket first second = -p286LieBracket second first := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

private theorem p286LieBracket_zero_right_local
    (first : P286LieBlockData) :
    p286LieBracket first 0 = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

private theorem p286LieBracket_zero_left_local
    (second : P286LieBlockData) :
    p286LieBracket 0 second = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

private theorem p286CoordinateLieBracket_antisymm
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket first second =
      -p286CoordinateLieBracket second first := by
  unfold p286CoordinateLieBracket
  rw [p286LieBracket_antisymm, map_neg]

private theorem p286CoordinateLieBracket_zero_right_local
    (first : P286CoordinateCarrier) :
    p286CoordinateLieBracket first 0 = 0 := by
  unfold p286CoordinateLieBracket
  rw [map_zero, p286LieBracket_zero_right_local, map_zero]

private theorem p286CoordinateLieBracket_zero_left_local
    (second : P286CoordinateCarrier) :
    p286CoordinateLieBracket 0 second = 0 := by
  unfold p286CoordinateLieBracket
  rw [map_zero, p286LieBracket_zero_left_local, map_zero]

private theorem mixing_canonical_coordinateBracket_eq_commutator :
    p286CoordinateLieBracket
        (p286CoordinateEquiv colorMixingP286ConnectionDirection)
        (p286CoordinateEquiv canonicalP286Generator) =
      p286CoordinateEquiv p286CommutatorProbeData := by
  rw [p286CoordinateLieBracket_equiv_apply]
  rfl

private theorem mixing_commutator_coordinateBracket_eq_neg_double :
    p286CoordinateLieBracket
        (p286CoordinateEquiv colorMixingP286ConnectionDirection)
        (p286CoordinateEquiv p286CommutatorProbeData) =
      -p286CoordinateEquiv p286DoubleCommutatorProbeData := by
  rw [p286CoordinateLieBracket_equiv_apply,
    p286LieBracket_antisymm, map_neg]
  rfl

private theorem sourceAffineExteriorZero_bracket_probe_pairing_eq_one :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket
          ((1 / 2 : ℝ) •
            p286CoordinateEquiv colorMixingP286ConnectionDirection)
          (p286CoordinateEquiv sourceAffineExteriorZero))
        (p286CoordinateEquiv p286CommutatorProbeData) = 1 := by
  rw [sourceAffineExteriorZero_coordinate_normalForm,
    p286CoordinateLieBracket_add_right,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLiePairing_smul_left,
    mixing_canonical_coordinateBracket_eq_commutator,
    mixing_commutator_coordinateBracket_eq_neg_double,
    p286CommutatorProbeData_pairing_self_eq_eight]
  rw [show -p286CoordinateEquiv p286DoubleCommutatorProbeData =
      (-1 : ℝ) • p286CoordinateEquiv p286DoubleCommutatorProbeData by simp,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    p286DoubleCommutator_pairing_commutator_eq_zero]
  norm_num

private theorem liftGaugeTwoFormOperator_fixedHodge_apply
    (form : P286GaugeTwoForm) (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge form pair =
      ![form 3, form 4, form 5, -form 0, -form 1, -form 2] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> rfl

private theorem p286FixedHodge_pairing_pairing
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
  simp_rw [liftGaugeTwoFormOperator_fixedHodge_apply]
  simp [lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_left,
    p286CoordinateLiePairing_neg_right]
  ring

private theorem liftGaugeTwoFormOperator_positiveSourceFrame_apply
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

/-- The actual constitutive auxiliary removes both Hodge operators, but not
the actual curvature derivative. -/
private theorem canonicalSourceNativeP286Input_p286DifferentialMomentum_normalForm
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input direction point =
      2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
              (nativeCurvatureCoordinate point) pair)
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
              direction pair) := by
  unfold p286GaugeConnectionBFDifferentialMomentum
  change
    abs (Matrix.det (canonicalSourceNativeP286Input.coframe point)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (canonicalSourceNativeP286Input.coframe point)
          (holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input point)
          direction = _
  rw [show canonicalSourceNativeP286Input.coframe point =
    canonicalPhysicalSource.coframeAt point by rfl,
    nativeAuxiliaryCoordinate_eq_constitutive,
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
    (nativeCurvatureCoordinate point)]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  let framedCurvature :=
    liftGaugeTwoFormOperator
      (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
      (nativeCurvatureCoordinate point)
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
      rw [p286FixedHodge_pairing_pairing]
      ring
    _ = _ := rfl

private theorem sourceAffineCoordinate_hasFDerivAt
    (formDirection : LorentzianIndex) (point : BasePoint) :
    HasFDerivAt (sourceAffineCoordinate formDirection)
      (sourceAffineIncrement formDirection) point := by
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

private theorem sourceAffineIncrement_coordinateDirection
    (formDirection derivativeDirection : LorentzianIndex) :
    sourceAffineIncrement formDirection
        (coordinateDirection derivativeDirection) =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv
          (sourceP286ExteriorDerivativeComponent
            positiveSmoothUnifiedSource.legacy
            derivativeDirection formDirection) := by
  simp only [sourceAffineIncrement, sourceP286AffineIncrementLinear]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [coordinateDirection, Fin.sum_univ_four]

private theorem sourceAffineCoordinate_origin
    (formDirection : LorentzianIndex) :
    sourceAffineCoordinate formDirection 0 =
      p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy
          formDirection) := by
  simp [sourceAffineCoordinate, sourceP286AffineConnectionCoordinate]

private theorem nativeP286ConnectionDerivative_coordinate
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286CoordinateEquiv
        (p286ConnectionDerivative
          (positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader)
          point derivativeDirection formDirection) =
      sourceAffineIncrement formDirection
        (coordinateDirection derivativeDirection) := by
  unfold p286ConnectionDerivative
  simp only [p286CoordinateEquiv.apply_symm_apply]
  have connectionCoordinate :
      (fun candidate =>
        p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection
              candidate formDirection)) =
        sourceAffineCoordinate formDirection := by
    funext candidate
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, sourceAffineCoordinate]
  rw [connectionCoordinate]
  unfold fieldDirectionalDerivative
  rw [(sourceAffineCoordinate_hasFDerivAt formDirection point).fderiv]

private theorem sourceAffineBracket_directionalDerivative_origin
    (first second derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => p286CoordinateLieBracket
          (sourceAffineCoordinate first point)
          (sourceAffineCoordinate second point))
        0 derivativeDirection =
      p286CoordinateLieBracket
          (sourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (sourceAffineCoordinate second 0) +
        p286CoordinateLieBracket
          (sourceAffineCoordinate first 0)
          (sourceAffineIncrement second
            (coordinateDirection derivativeDirection)) := by
  have derivative :=
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (sourceAffineCoordinate_hasFDerivAt first 0)
        (sourceAffineCoordinate_hasFDerivAt second 0)).fderiv
  have evaluated := congrArg
    (fun linear : BasePoint →L[ℝ] P286CoordinateCarrier =>
      linear (coordinateDirection derivativeDirection)) derivative
  change
    (fderiv ℝ
      (fun point => p286CoordinateLieBracket
        (sourceAffineCoordinate first point)
        (sourceAffineCoordinate second point)) 0)
        (coordinateDirection derivativeDirection) =
      p286CoordinateLieBracket (sourceAffineCoordinate first 0)
          (sourceAffineIncrement second
            (coordinateDirection derivativeDirection)) +
        p286CoordinateLieBracket
          (sourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (sourceAffineCoordinate second 0) at evaluated
  unfold fieldDirectionalDerivative
  change fderiv ℝ
    (fun point => p286CoordinateLieBracket
      (sourceAffineCoordinate first point)
      (sourceAffineCoordinate second point)) 0
      (coordinateDirection derivativeDirection) = _
  calc
    _ = p286CoordinateLieBracket
          (sourceAffineCoordinate first 0)
          (sourceAffineIncrement second
            (coordinateDirection derivativeDirection)) +
        p286CoordinateLieBracket
          (sourceAffineIncrement first
            (coordinateDirection derivativeDirection))
          (sourceAffineCoordinate second 0) := by
      exact evaluated
    _ = _ := add_comm _ _

private theorem nativeCurvatureCoordinate_normalForm
    (point : BasePoint) (pair : Fin 6) :
    nativeCurvatureCoordinate point pair =
      p286CoordinateEquiv
          (sourceP286ExteriorDerivative
            positiveSmoothUnifiedSource.legacy pair) +
        p286CoordinateLieBracket
          (sourceAffineCoordinate (pairFirst pair) point)
          (sourceAffineCoordinate (pairSecond pair) point) := by
  unfold nativeCurvatureCoordinate holonomicGaugeCurvature
  rw [map_add, map_sub,
    nativeP286ConnectionDerivative_coordinate,
    nativeP286ConnectionDerivative_coordinate,
    sourceAffineIncrement_coordinateDirection,
    sourceAffineIncrement_coordinateDirection,
    sourceP286ExteriorDerivativeComponent_antisymm
      positiveSmoothUnifiedSource.legacy (pairSecond pair) (pairFirst pair),
    sourceP286ExteriorDerivativeComponent_pair]
  simp only [map_neg]
  have firstCoordinate :
      p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection point
              (pairFirst pair)) =
        sourceAffineCoordinate (pairFirst pair) point := by
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, sourceAffineCoordinate]
  have secondCoordinate :
      p286CoordinateEquiv
          ((positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader).gaugeConnection point
              (pairSecond pair)) =
        sourceAffineCoordinate (pairSecond pair) point := by
    simp only [positiveSourceNativeKinematicSeed,
      installSourceP286AffineConnection_gaugeConnection]
    simp [sourceP286AffineConnectionField, sourceAffineCoordinate]
  have firstData :
      (positiveSourceNativeKinematicSeed
        residualLimitLorentzCarrierReader).gaugeConnection point
          (pairFirst pair) =
        p286CoordinateEquiv.symm
          (sourceAffineCoordinate (pairFirst pair) point) := by
    apply p286CoordinateEquiv.injective
    rw [firstCoordinate, p286CoordinateEquiv.apply_symm_apply]
  have secondData :
      (positiveSourceNativeKinematicSeed
        residualLimitLorentzCarrierReader).gaugeConnection point
          (pairSecond pair) =
        p286CoordinateEquiv.symm
          (sourceAffineCoordinate (pairSecond pair) point) := by
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
        (sourceAffineCoordinate (pairFirst pair) point)
        (sourceAffineCoordinate (pairSecond pair) point) by
    unfold p286CoordinateLieBracket
    rw [firstData, secondData]]
  module

private theorem nativeCurvatureCoordinate_directionalDerivative_origin
    (pair : Fin 6) (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => nativeCurvatureCoordinate point pair)
        0 derivativeDirection =
      p286CoordinateLieBracket
          (sourceAffineIncrement (pairFirst pair)
            (coordinateDirection derivativeDirection))
          (sourceAffineCoordinate (pairSecond pair) 0) +
        p286CoordinateLieBracket
          (sourceAffineCoordinate (pairFirst pair) 0)
          (sourceAffineIncrement (pairSecond pair)
            (coordinateDirection derivativeDirection)) := by
  have curvatureFunction :
      (fun point => nativeCurvatureCoordinate point pair) =
        fun point =>
          p286CoordinateEquiv
              (sourceP286ExteriorDerivative
                positiveSmoothUnifiedSource.legacy pair) +
            p286CoordinateLieBracket
              (sourceAffineCoordinate (pairFirst pair) point)
              (sourceAffineCoordinate (pairSecond pair) point) := by
    funext point
    exact nativeCurvatureCoordinate_normalForm point pair
  have bracketDerivative :=
    sourceAffineBracket_directionalDerivative_origin
      (pairFirst pair) (pairSecond pair) derivativeDirection
  unfold fieldDirectionalDerivative at bracketDerivative ⊢
  rw [curvatureFunction, fderiv_const_add]
  exact bracketDerivative

private def nativeCurvatureFDeriv
    (pair : Fin 6) : BasePoint →L[ℝ] P286CoordinateCarrier :=
  (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.precompR
      BasePoint (sourceAffineCoordinate (pairFirst pair) 0)
      (sourceAffineIncrement (pairSecond pair))) +
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.precompL
      BasePoint (sourceAffineIncrement (pairFirst pair))
      (sourceAffineCoordinate (pairSecond pair) 0))

private theorem nativeCurvatureCoordinate_hasFDerivAt_origin
    (pair : Fin 6) :
    HasFDerivAt (fun point => nativeCurvatureCoordinate point pair)
      (nativeCurvatureFDeriv pair) 0 := by
  have bracketDerivative :=
    p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (sourceAffineCoordinate_hasFDerivAt (pairFirst pair) 0)
        (sourceAffineCoordinate_hasFDerivAt (pairSecond pair) 0)
  have withConstant := bracketDerivative.const_add
    (p286CoordinateEquiv
      (sourceP286ExteriorDerivative positiveSmoothUnifiedSource.legacy pair))
  have functionEquality :
      (fun point => nativeCurvatureCoordinate point pair) =
        fun point =>
          p286CoordinateEquiv
              (sourceP286ExteriorDerivative
                positiveSmoothUnifiedSource.legacy pair) +
            p286CoordinateLieBracket
              (sourceAffineCoordinate (pairFirst pair) point)
              (sourceAffineCoordinate (pairSecond pair) point) := by
    funext point
    exact nativeCurvatureCoordinate_normalForm point pair
  rw [functionEquality]
  exact withConstant

private theorem fieldDirectionalDerivative_pairing_const
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

private theorem sourceAffineIncrement_zero_direction_one :
    sourceAffineIncrement 0 (coordinateDirection 1) =
      -(1 / 2 : ℝ) • p286CoordinateEquiv sourceAffineExteriorZero := by
  rw [sourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent, sourceAffineExteriorZero]

private theorem sourceAffineIncrement_one_direction_one :
    sourceAffineIncrement 1 (coordinateDirection 1) = 0 := by
  rw [sourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

private theorem sourceAffineCoordinate_zero_origin :
    sourceAffineCoordinate 0 0 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorCartanP286ConnectionDirection := by
  rw [sourceAffineCoordinate_origin,
    positiveSourceP286Potential_zero_coordinate]

private theorem sourceAffineCoordinate_one_origin :
    sourceAffineCoordinate 1 0 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv colorMixingP286ConnectionDirection := by
  rw [sourceAffineCoordinate_origin,
    positiveSourceP286Potential_one_coordinate]

private theorem mixing_exteriorZero_raw_bracket_pairing_eq_two :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorMixingP286ConnectionDirection)
          (p286CoordinateEquiv sourceAffineExteriorZero))
        (p286CoordinateEquiv p286CommutatorProbeData) = 2 := by
  have scaled := sourceAffineExteriorZero_bracket_probe_pairing_eq_one
  rw [p286CoordinateLieBracket_smul_left,
    p286CoordinateLiePairing_smul_left] at scaled
  norm_num at scaled ⊢
  linarith

private theorem nativeCurvatureCoordinate_zero_direction_one_pairing_eq_half :
    p286CoordinateLiePairing
        (fieldDirectionalDerivative
          (fun point => nativeCurvatureCoordinate point 0) 0 1)
        (p286CoordinateEquiv p286CommutatorProbeData) = 1 / 2 := by
  rw [nativeCurvatureCoordinate_directionalDerivative_origin]
  simp only [pairFirst, pairSecond, Matrix.cons_val_zero]
  rw [sourceAffineIncrement_zero_direction_one,
    sourceAffineIncrement_one_direction_one,
    sourceAffineCoordinate_one_origin,
    p286CoordinateLieBracket_zero_right_local,
    add_zero,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLieBracket_antisymm]
  rw [show -p286CoordinateLieBracket
      (p286CoordinateEquiv colorMixingP286ConnectionDirection)
      (p286CoordinateEquiv sourceAffineExteriorZero) =
      (-1 : ℝ) • p286CoordinateLieBracket
        (p286CoordinateEquiv colorMixingP286ConnectionDirection)
        (p286CoordinateEquiv sourceAffineExteriorZero) by simp,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    mixing_exteriorZero_raw_bracket_pairing_eq_two]
  norm_num

private theorem sourceAffineCoordinate_two_origin :
    sourceAffineCoordinate 2 0 = 0 := by
  rw [sourceAffineCoordinate_origin]
  simp [sourceP286Potential]

private theorem sourceAffineCoordinate_three_origin :
    sourceAffineCoordinate 3 0 = 0 := by
  rw [sourceAffineCoordinate_origin]
  simp [sourceP286Potential]

private theorem sourceAffineIncrement_two_direction_two :
    sourceAffineIncrement 2 (coordinateDirection 2) = 0 := by
  rw [sourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

private theorem sourceAffineIncrement_three_direction_three :
    sourceAffineIncrement 3 (coordinateDirection 3) = 0 := by
  rw [sourceAffineIncrement_coordinateDirection]
  simp [sourceP286ExteriorDerivativeComponent]

private theorem nativeCurvatureCoordinate_one_direction_two_eq_zero :
    fieldDirectionalDerivative
        (fun point => nativeCurvatureCoordinate point 1) 0 2 = 0 := by
  rw [nativeCurvatureCoordinate_directionalDerivative_origin]
  simp only [pairFirst, pairSecond, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [sourceAffineCoordinate_two_origin,
    sourceAffineIncrement_two_direction_two]
  simp

private theorem nativeCurvatureCoordinate_two_direction_three_eq_zero :
    fieldDirectionalDerivative
        (fun point => nativeCurvatureCoordinate point 2) 0 3 = 0 := by
  rw [nativeCurvatureCoordinate_directionalDerivative_origin]
  change
    p286CoordinateLieBracket
        (sourceAffineIncrement 0 (coordinateDirection 3))
        (sourceAffineCoordinate 3 0) +
      p286CoordinateLieBracket (sourceAffineCoordinate 0 0)
        (sourceAffineIncrement 3 (coordinateDirection 3)) = 0
  rw [sourceAffineCoordinate_three_origin,
    sourceAffineIncrement_three_direction_three]
  simp

private theorem nativeCurvatureCoordinate_origin
    (pair : Fin 6) :
    nativeCurvatureCoordinate 0 pair =
      p286CoordinateEquiv
        (sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy pair) := by
  unfold nativeCurvatureCoordinate
  rw [show positiveSourceNativeKinematicSeed
      residualLimitLorentzCarrierReader =
      installSourceP286AffineConnection positiveSmoothUnifiedSource.legacy
        (installPositiveSourceNativeGravityKinematics
          residualLimitLorentzCarrierReader) by rfl]
  rw [holonomicGaugeCurvature_installSourceP286AffineConnection_origin]

private theorem nativeCurvatureCoordinate_origin_five_eq_zero :
    nativeCurvatureCoordinate 0 5 = 0 := by
  rw [nativeCurvatureCoordinate_origin,
    positiveSourceP286TargetCurvature_apply]
  split_ifs with h
  · omega
  · rfl

private theorem nativeMomentum_probe_direction_zero
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe) point =
      0 := by
  rw [canonicalSourceNativeP286Input_p286DifferentialMomentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]

private theorem nativeMomentum_probe_direction_one
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe) point =
      2 * p286CoordinateLiePairing
        (nativeCurvatureCoordinate point 0)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalSourceNativeP286Input_p286DifferentialMomentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right]

private theorem nativeMomentum_probe_direction_two
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe) point =
      2 * p286CoordinateLiePairing
        (nativeCurvatureCoordinate point 1 +
          point 2 • nativeCurvatureCoordinate point 5)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalSourceNativeP286Input_p286DifferentialMomentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right]

private theorem nativeMomentum_probe_direction_three
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe) point =
      2 * p286CoordinateLiePairing
        (nativeCurvatureCoordinate point 2 -
          point 2 • nativeCurvatureCoordinate point 4)
        (p286CoordinateEquiv p286CommutatorProbeData) := by
  rw [canonicalSourceNativeP286Input_p286DifferentialMomentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply]
  simp [p286GaugeExteriorDerivativeDirection, p286CommutatorProbe,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right]

private theorem nativeMomentum_probe_direction_zero_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe))
        0 0 = 0 := by
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 p286CommutatorProbe) =
        fun _ => 0 := by
    funext point
    exact nativeMomentum_probe_direction_zero point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

private theorem nativeMomentum_probe_direction_one_derivative_eq_one :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe))
        0 1 = 1 := by
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (nativeCurvatureCoordinate point 0)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact nativeMomentum_probe_direction_one point
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (nativeCurvatureCoordinate_hasFDerivAt_origin 0)
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 1 = 1
  rw [fieldDirectionalDerivative_pairing_const
    (fun point => nativeCurvatureCoordinate point 0)
    (nativeCurvatureFDeriv 0) 0 1
    (p286CoordinateEquiv p286CommutatorProbeData)
    (nativeCurvatureCoordinate_hasFDerivAt_origin 0)]
  rw [nativeCurvatureCoordinate_zero_direction_one_pairing_eq_half]
  norm_num

private theorem nativeFramedCurvatureOne_direction_two_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          nativeCurvatureCoordinate point 1 +
            point 2 • nativeCurvatureCoordinate point 5)
        0 2 = 0 := by
  let productDerivative : BasePoint →L[ℝ] P286CoordinateCarrier :=
    (p286BaseCoordinate 2 0) • nativeCurvatureFDeriv 5 +
      (p286BaseCoordinate 2).smulRight
        (nativeCurvatureCoordinate 0 5)
  have productHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            point 2 • nativeCurvatureCoordinate point 5)
          productDerivative 0 := by
    have rawDerivative :=
      (p286BaseCoordinate 2).hasFDerivAt.smul
        (nativeCurvatureCoordinate_hasFDerivAt_origin 5)
    change HasFDerivAt
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • nativeCurvatureCoordinate point 5)
      productDerivative 0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            nativeCurvatureCoordinate point 1 +
              point 2 • nativeCurvatureCoordinate point 5)
          (nativeCurvatureFDeriv 1 + productDerivative) 0 := by
    have rawDerivative :=
      (nativeCurvatureCoordinate_hasFDerivAt_origin 1).add
        productHasDerivative
    change HasFDerivAt
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 1 +
          point 2 • nativeCurvatureCoordinate point 5)
      (nativeCurvatureFDeriv 1 + productDerivative) 0 at rawDerivative
    exact rawDerivative
  have curvatureOneLinearZero :
      nativeCurvatureFDeriv 1 (coordinateDirection 2) = 0 := by
    have directionalZero :=
      nativeCurvatureCoordinate_one_direction_two_eq_zero
    unfold fieldDirectionalDerivative at directionalZero
    rw [(nativeCurvatureCoordinate_hasFDerivAt_origin 1).fderiv]
      at directionalZero
    exact directionalZero
  change
    (fderiv ℝ
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 1 +
          point 2 • nativeCurvatureCoordinate point 5) 0)
        (coordinateDirection 2) = 0
  rw [framedHasDerivative.fderiv]
  simp only [add_apply]
  rw [curvatureOneLinearZero]
  simp [productDerivative,
    nativeCurvatureCoordinate_origin_five_eq_zero,
    p286BaseCoordinate_apply, coordinateDirection]

private theorem nativeFramedCurvatureTwo_direction_three_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          nativeCurvatureCoordinate point 2 -
            point 2 • nativeCurvatureCoordinate point 4)
        0 3 = 0 := by
  let productDerivative : BasePoint →L[ℝ] P286CoordinateCarrier :=
    (p286BaseCoordinate 2 0) • nativeCurvatureFDeriv 4 +
      (p286BaseCoordinate 2).smulRight
        (nativeCurvatureCoordinate 0 4)
  have productHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            point 2 • nativeCurvatureCoordinate point 4)
          productDerivative 0 := by
    have rawDerivative :=
      (p286BaseCoordinate 2).hasFDerivAt.smul
        (nativeCurvatureCoordinate_hasFDerivAt_origin 4)
    change HasFDerivAt
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • nativeCurvatureCoordinate point 4)
      productDerivative 0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            nativeCurvatureCoordinate point 2 -
              point 2 • nativeCurvatureCoordinate point 4)
          (nativeCurvatureFDeriv 2 - productDerivative) 0 := by
    have rawDerivative :=
      (nativeCurvatureCoordinate_hasFDerivAt_origin 2).sub
        productHasDerivative
    change HasFDerivAt
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 2 -
          point 2 • nativeCurvatureCoordinate point 4)
      (nativeCurvatureFDeriv 2 - productDerivative) 0 at rawDerivative
    exact rawDerivative
  have curvatureTwoLinearZero :
      nativeCurvatureFDeriv 2 (coordinateDirection 3) = 0 := by
    have directionalZero :=
      nativeCurvatureCoordinate_two_direction_three_eq_zero
    unfold fieldDirectionalDerivative at directionalZero
    rw [(nativeCurvatureCoordinate_hasFDerivAt_origin 2).fderiv]
      at directionalZero
    exact directionalZero
  change
    (fderiv ℝ
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 2 -
          point 2 • nativeCurvatureCoordinate point 4) 0)
        (coordinateDirection 3) = 0
  rw [framedHasDerivative.fderiv]
  simp only [sub_apply]
  rw [curvatureTwoLinearZero]
  simp [productDerivative,
    p286BaseCoordinate_apply, coordinateDirection]

private theorem nativeMomentum_probe_direction_two_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe))
        0 2 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    nativeCurvatureCoordinate point 1 +
      point 2 • nativeCurvatureCoordinate point 5
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have productDifferentiable :
      DifferentiableAt ℝ
        (fun point : BasePoint =>
          point 2 • nativeCurvatureCoordinate point 5) 0 := by
    have rawDerivative :=
      ((p286BaseCoordinate 2).hasFDerivAt.smul
        (nativeCurvatureCoordinate_hasFDerivAt_origin 5)).differentiableAt
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • nativeCurvatureCoordinate point 5)
      0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 := by
    have rawDerivative :=
      (nativeCurvatureCoordinate_hasFDerivAt_origin 1).differentiableAt.add
        productDifferentiable
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 1 +
          point 2 • nativeCurvatureCoordinate point 5) 0 at rawDerivative
    exact rawDerivative
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact nativeMomentum_probe_direction_two point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 2 = 0
  rw [fieldDirectionalDerivative_pairing_const framedField
    (fderiv ℝ framedField 0) 0 2
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt]
  rw [nativeFramedCurvatureOne_direction_two_eq_zero]
  simp

private theorem nativeMomentum_probe_direction_three_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe))
        0 3 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    nativeCurvatureCoordinate point 2 -
      point 2 • nativeCurvatureCoordinate point 4
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv p286CommutatorProbeData)
  have productDifferentiable :
      DifferentiableAt ℝ
        (fun point : BasePoint =>
          point 2 • nativeCurvatureCoordinate point 4) 0 := by
    have rawDerivative :=
      ((p286BaseCoordinate 2).hasFDerivAt.smul
        (nativeCurvatureCoordinate_hasFDerivAt_origin 4)).differentiableAt
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • nativeCurvatureCoordinate point 4)
      0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 := by
    have rawDerivative :=
      (nativeCurvatureCoordinate_hasFDerivAt_origin 2).differentiableAt.sub
        productDifferentiable
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        nativeCurvatureCoordinate point 2 -
          point 2 • nativeCurvatureCoordinate point 4) 0 at rawDerivative
    exact rawDerivative
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv p286CommutatorProbeData) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 p286CommutatorProbe) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact nativeMomentum_probe_direction_three point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 3 = 0
  rw [fieldDirectionalDerivative_pairing_const framedField
    (fderiv ℝ framedField 0) 0 3
    (p286CoordinateEquiv p286CommutatorProbeData)
    framedDifferentiable.hasFDerivAt]
  rw [nativeFramedCurvatureTwo_direction_three_eq_zero]
  simp

theorem canonicalSourceNativeP286Input_p286Divergence_probe_eq_one :
    p286GaugeConnectionBFDifferentialMomentumDivergence canonicalSourceNativeP286Input
        p286CommutatorProbe 0 = 1 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [Fin.sum_univ_four,
    nativeMomentum_probe_direction_zero_derivative_eq_zero,
    nativeMomentum_probe_direction_one_derivative_eq_one,
    nativeMomentum_probe_direction_two_derivative_eq_zero,
    nativeMomentum_probe_direction_three_derivative_eq_zero]
  norm_num

private theorem canonicalSourceNativeP286Input_p286AuxiliaryCoordinate_origin_eq_reference :
    holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input 0 =
      positiveResidualLimitP286AuxiliaryCoordinate 0 := by
  have curvatureEq :=
    positiveSourceP286AffineConnection_actualCurvature
      (installPositiveSourceNativeGravityKinematics
        residualLimitLorentzCarrierReader)
  change
    (fun pair => p286CoordinateEquiv
      (generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
        (positiveSmoothUnifiedSource.legacy.coframeAt 0)
        (holonomicGaugeCurvature
          (positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader) 0) pair)) = _
  change
    holonomicGaugeCurvature
        (positiveSourceNativeKinematicSeed residualLimitLorentzCarrierReader)
        0 = sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy
      at curvatureEq
  rw [curvatureEq]
  rfl

private theorem canonicalSourceNativeP286Input_p286BFAlgebraic_probe_eq_neg_two :
    p286GaugeBFAlgebraicCoefficient canonicalSourceNativeP286Input
      p286CommutatorProbe 0 = -2 := by
  unfold p286GaugeBFAlgebraicCoefficient
  rw [canonicalSourceNativeP286Input_p286AuxiliaryCoordinate_origin_eq_reference]
  change positiveResidualLimitP286BFAlgebraicResponse
      p286CommutatorProbe = -2
  exact positiveResidualLimitP286BFAlgebraicResponse_probe_eq_neg_two

private theorem canonicalSourceNativeP286Input_scalar_eq_constantVacuum :
    canonicalSourceNativeP286Input.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change positiveResidualLimitSixFieldCarrier.scalar = _
  exact positiveResidualLimitSixFieldCarrier_scalar_eq_constantVacuum

private theorem canonicalSourceNativeP286Input_scalarCovariantDerivative_origin_eq_source
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative canonicalSourceNativeP286Input 0 direction =
      positiveSourceOriginScalarGaugeDerivative direction := by
  unfold holonomicScalarCovariantDerivative
    positiveSourceOriginScalarGaugeDerivative
  rw [canonicalSourceNativeP286Input_scalar_eq_constantVacuum,
    positiveSourceNativeAlgebraicEliminationUpdate_gaugeConnection]
  simp [sourceP286AffineConnectionField_origin,
    fieldDirectionalDerivative]

private theorem canonicalSourceNativeP286Input_p286ScalarCurrent_probe_eq_zero :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input p286CommutatorProbe 0 = 0 := by
  have coframeOrigin :
      (toContinuumPointField canonicalSourceNativeP286Input 0).coframe = 1 := by
    change canonicalSourceNativeP286Input.coframe 0 = 1
    rw [positiveSourceNativeAlgebraicEliminationUpdate_coframe]
    exact positiveSmoothUnifiedSource.legacy.coframeAt_zero
  have scalarOrigin :
      canonicalSourceNativeP286Input.scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    rw [canonicalSourceNativeP286Input_scalar_eq_constantVacuum]
  have covariantDerivativeOrigin :
      (toContinuumPointField canonicalSourceNativeP286Input 0).scalarCovariantDerivative =
        positiveSourceOriginScalarGaugeDerivative := by
    funext direction
    exact canonicalSourceNativeP286Input_scalarCovariantDerivative_origin_eq_source direction
  have currentEq :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          canonicalSourceNativeP286Input p286CommutatorProbe 0 =
        positiveSourceOriginP286ScalarCurrent p286CommutatorProbe := by
    unfold p286ScalarCurrentCoefficient
      scalarGaugeConnectionKineticFirstVariationDensity
      positiveSourceOriginP286ScalarCurrent
      holonomicScalarGaugeConnectionVariation
    rw [coframeOrigin, scalarOrigin, covariantDerivativeOrigin]
    simp [generatedVolumeDensity, scalarFrameRelativeCovariantDerivative,
      p286GaugeConnectionMotherVariation]
    rw [coframeOrigin, Matrix.det_one, abs_one, one_mul]
  rw [currentEq]
  exact positiveSourceOriginP286ScalarCurrent_eq_zero p286CommutatorProbe

private theorem canonicalSourceNativeP286Input_p286MatterCurrent_probe_eq_zero :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input p286CommutatorProbe 0 = 0 := by
  unfold p286MatterCurrentCoefficient
    matterGaugeConnectionFirstVariationDensity
  have matterZero : canonicalSourceNativeP286Input.matter = 0 := by
    rfl
  have conjugateMatterZero : canonicalSourceNativeP286Input.conjugateMatter = 0 := by
    rfl
  rw [show (toContinuumPointField canonicalSourceNativeP286Input 0).conjugateMatter = 0 by
    change canonicalSourceNativeP286Input.conjugateMatter 0 = 0
    rw [conjugateMatterZero]
    rfl]
  simp

theorem canonicalSourceNativeP286Input_p286Residual_probe_eq_neg_three :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        canonicalSourceNativeP286Input p286CommutatorProbe 0 = -3 := by
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rw [
    canonicalSourceNativeP286Input_p286BFAlgebraic_probe_eq_neg_two,
    canonicalSourceNativeP286Input_p286Divergence_probe_eq_one,
    canonicalSourceNativeP286Input_p286ScalarCurrent_probe_eq_zero,
    canonicalSourceNativeP286Input_p286MatterCurrent_probe_eq_zero]
  norm_num

theorem canonicalSourceNativeP286Input_p286Trace_probe_eq_neg_three_halves :
    ((currentJointShellResidualTrace positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input) 0).eulerLagrange.p286GaugeConnection
        p286CommutatorProbe = -(3 / 2 : ℝ) := by
  rw [currentJointShellResidualTrace_eq_scalarTrace]
  change
    positiveSmoothUnifiedSource.legacy.sigma *
      p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource canonicalSourceNativeP286Input
        p286CommutatorProbe 0 = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    canonicalSourceNativeP286Input_p286Residual_probe_eq_neg_three]
  norm_num

theorem canonicalSourceNativeP286Response_p286LiftDefect_probe_eq_neg_three_halves :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      canonicalSourceNativeP286Input) 0).eulerLagrange.p286GaugeConnection
        p286CommutatorProbe = -(3 / 2 : ℝ) := by
  change
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        canonicalSourceNativeP286Response p286CommutatorProbe 0 -
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource canonicalSourceNativeP286Input
          p286CommutatorProbe 0 = _
  have unchanged :
      p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          canonicalSourceNativeP286Response p286CommutatorProbe 0 =
        p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource canonicalSourceNativeP286Input
          p286CommutatorProbe 0 := by
    rfl
  rw [unchanged,
    canonicalSourceNativeP286Input_p286Residual_probe_eq_neg_three,
    positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num

theorem canonicalSourceNativeP286Response_p286LiftDefect_probe_ne_zero :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      canonicalSourceNativeP286Input) 0).eulerLagrange.p286GaugeConnection
        p286CommutatorProbe ≠ 0 := by
  rw [canonicalSourceNativeP286Response_p286LiftDefect_probe_eq_neg_three_halves]
  norm_num

theorem canonicalSourceNativeP286Response_liftDefect_origin_ne_zero :
    currentJointShellStateLiftDefect positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      canonicalSourceNativeP286Input 0 ≠ 0 := by
  intro defectZero
  have projected := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.p286GaugeConnection p286CommutatorProbe)
    defectZero
  rw [canonicalSourceNativeP286Response_p286LiftDefect_probe_eq_neg_three_halves] at projected
  norm_num at projected


/-- C3h71's canonical full-defect carrier therefore has the independently
computed P286 responsibility `-3/2`. -/
theorem algebraicKeepResponseLiftDefect_reference_p286_probe_eq_neg_three_halves :
    (algebraicKeepResponseLiftDefect
      residualLimitLorentzCarrierReader).eulerLagrange.p286GaugeConnection
        p286CommutatorProbe = -(3 / 2 : ℝ) := by
  change
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      canonicalSourceNativeP286Input) 0).eulerLagrange.p286GaugeConnection
        p286CommutatorProbe = -(3 / 2 : ℝ)
  exact
    canonicalSourceNativeP286Response_p286LiftDefect_probe_eq_neg_three_halves

/-- Independent P286 witness that the C3h70 canonical full defect is nonzero. -/
theorem algebraicKeepResponseLiftDefect_reference_ne_zero :
    algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader ≠ 0 := by
  intro defectZero
  have coordinateZero :
      (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.p286GaugeConnection
          p286CommutatorProbe = 0 := by
    simpa using congrArg
      (fun residual : CurrentPointwiseJointShellResidualCarrier =>
        residual.eulerLagrange.p286GaugeConnection p286CommutatorProbe)
      defectZero
  rw [algebraicKeepResponseLiftDefect_reference_p286_probe_eq_neg_three_halves]
    at coordinateZero
  norm_num at coordinateZero

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseP286Defect
