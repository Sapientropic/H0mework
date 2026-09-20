import H0mework.Physics.Lorentz.ResidualLimitLorentzOriginResponsePreimage
import H0mework.Physics.Matter.ResidualLimitConjugateMatterJointChannelAudit
import H0mework.Physics.Admission.ResidualLimitScalarJointChannelAudit
import H0mework.Physics.Coframe.CoframeSectorStress
import H0mework.Physics.Admission.GravityMultiplierResidualNoninjectivity
import H0mework.Physics.Coframe.CoframeTwoFormPairing
import H0mework.Physics.Geometry.GravityAlgebraicShellLocus
import H0mework.Physics.GaugeAction.ResidualLimitP286BFBalanceDecision

/-!
# S9-C3h43: residual-limit coframe balance decision

This module decides only the absolute `q_D` reader's coframe balance at the
origin, where its point field equals the reference point field.  It accepts no
stress, residual, zero, stationarity, multiplier, dual, or matter-orbit
receipt.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitCoframeBalanceDecision

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityMultiplierResidualNoninjectivity
open StageNineGravityAlgebraicShellLocus
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitConjugateMatterJointChannelAudit
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzOriginResponsePreimage
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitP286BFBalanceDecision
open StageNineResidualLimitScalarBalanceClosure
open StageNineResidualLimitScalarJointChannelAudit
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000

abbrev qDReader : StageNineHolonomicConfiguration :=
  residualLimitArbitraryOriginReader
    residualLimitReferenceDivergenceOriginPreimage

abbrev referenceOriginField : StageNineContinuumPointField :=
  toContinuumPointField residualLimitLorentzCarrierReader 0

/-! ## The q_D point field is the reference point field -/

theorem qDReader_matterCovariantDerivative_origin_zero :
    holonomicMatterCovariantDerivative qDReader 0 = 0 :=
  holonomicMatterCovariantDerivative_zero_of_matter_eq_zero qDReader (by rfl)

theorem qDReader_pointField_origin_eq_reference :
    toContinuumPointField qDReader 0 =
      toContinuumPointField residualLimitLorentzCarrierReader 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  · change holonomicGravityCurvature qDReader 0 =
      holonomicGravityCurvature residualLimitLorentzCarrierReader 0
    rw [residualLimitArbitraryOriginReader_curvature_origin]
    exact (residualLimitExtension_gravityCurvature_origin
      residualLimitLorentzCarrierReader
      residualLimitLorentzCarrierReader_extends).symm
  · change holonomicMatterCovariantDerivative qDReader 0 =
      holonomicMatterCovariantDerivative residualLimitLorentzCarrierReader 0
    rw [qDReader_matterCovariantDerivative_origin_zero,
      jointAuditReference_matterCovariantDerivative_origin_zero]

theorem qDReader_coframeResidual_origin_eq_reference :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField qDReader 0) =
      coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
  rw [qDReader_pointField_origin_eq_reference]

/-! ## Multiplier jurisdiction at this point -/

theorem referencePointField_simplicity :
    (toContinuumPointField residualLimitLorentzCarrierReader 0).gravityAuxiliary =
      physicalIIPlusBivector
        (toContinuumPointField residualLimitLorentzCarrierReader 0).coframe := by
  change residualLimitLorentzCarrierReader.gravityAuxiliary 0 =
    physicalIIPlusBivector (residualLimitLorentzCarrierReader.coframe 0)
  exact residualLimitExtension_has_simplicityMouth
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends

theorem referencePointField_multiplier_zero :
    (toContinuumPointField residualLimitLorentzCarrierReader 0).gravitySimplicityMultiplier = 0 :=
  rfl

theorem referenceOriginField_coframe_eq_one :
    referenceOriginField.coframe = 1 := by
  change positiveResidualLimitSixFieldCarrier.coframe 0 = 1
  exact positiveResidualLimitSixFieldCarrier_coframe_origin_eq_one

theorem referenceOriginField_gravityCurvature_eq_constitutive :
    referenceOriginField.gravityCurvature =
      gravityInternalDualEquiv referenceOriginField.gravityAuxiliary := by
  change holonomicGravityCurvature residualLimitLorentzCarrierReader 0 =
    gravityInternalDualEquiv
      (residualLimitLorentzCarrierReader.gravityAuxiliary 0)
  rw [residualLimitExtension_gravityCurvature_origin
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends]
  rfl

theorem referenceOriginField_gravityAuxiliary_eq_physical :
    referenceOriginField.gravityAuxiliary =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  change residualLimitLorentzCarrierReader.gravityAuxiliary 0 = _
  rw [residualLimitLorentzCarrierReader_gravityAuxiliary]
  congr 1
  exact ProofFreeRicherAnholonomicSource.Source.coframeAt_zero
    canonicalPhysicalSource

theorem coframeGaugeSpacetimeHodgeLinear_one :
    coframeGaugeSpacetimeHodgeLinear (1 : LorentzianCoframe) =
      lorentzianCoframeHodgeEquiv.toLinearMap := by
  rw [coframeGaugeSpacetimeHodgeLinear, inverseCoframeTwoFormLinear,
    inv_one, coframeTwoFormLinear_one]
  rfl

def identityPhysicalIIPlusBivector : PhysicalBivector :=
  ![![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1],
    ![-1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0]]

theorem physicalIIPlusBivector_one_eq_identityCoordinates :
    physicalIIPlusBivector (1 : LorentzianCoframe) =
      identityPhysicalIIPlusBivector := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [identityPhysicalIIPlusBivector, physicalIIPlusBivector,
      internalBivectorDual, lorentzianCoframeHodge, coframeWedge,
      pairFirst, pairSecond, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val']

theorem gravitySpacetimeHodge_one_constitutive :
    gravitySpacetimeHodge (1 : LorentzianCoframe)
        (gravityInternalDualEquiv
          (physicalIIPlusBivector (1 : LorentzianCoframe))) =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  rw [currentGravityShellCurvature_eq_negCoframeWedge]
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [gravitySpacetimeHodge,
      coframeGaugeSpacetimeHodgeLinear_one,
      physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
      coframeWedge, pairFirst, pairSecond, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val]

theorem gravityCoframePairing_one_physical_self :
    gravityCoframePairing (1 : LorentzianCoframe)
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (physicalIIPlusBivector (1 : LorentzianCoframe)) = -6 := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
  simp_rw [coframeTwoFormLinear_one]
  rw [physicalIIPlusBivector_one_eq_identityCoordinates]
  simp [identityPhysicalIIPlusBivector, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val',
    Fin.sum_univ_six] ;
  norm_num

/- This direct finite-coordinate probe is intentionally local. -/
theorem referenceOriginField_gravityBFDensity_eq_neg_three :
    generatedGravityBFDensity referenceOriginField = -3 := by
  unfold generatedGravityBFDensity
  rw [referenceOriginField_gravityCurvature_eq_constitutive,
    referenceOriginField_gravityAuxiliary_eq_physical,
    referenceOriginField_coframe_eq_one]
  rw [gravitySpacetimeHodge_one_constitutive,
    gravityCoframePairing_one_physical_self]
  norm_num

/-! ## Actual P286 gauge density at the same point -/

abbrev referenceP286CurvatureCoordinate : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (referenceOriginField.gaugeCurvature pair)

abbrev referenceP286AuxiliaryCoordinate : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (referenceOriginField.gaugeAuxiliary pair)

theorem referenceP286CurvatureCoordinate_apply (pair : Fin 6) :
    referenceP286CurvatureCoordinate pair =
      if pair = 0 then
        (1 / 4 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  change p286CoordinateEquiv
      (holonomicGaugeCurvature residualLimitLorentzCarrierReader 0 pair) = _
  rw [residualLimitExtension_gaugeCurvature_origin
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends]
  exact positiveSourceP286TargetCurvature_apply pair

theorem referenceP286AuxiliaryCoordinate_apply (pair : Fin 6) :
    referenceP286AuxiliaryCoordinate pair =
      if pair = 3 then
        (1 / 2 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  change positiveResidualLimitP286AuxiliaryCoordinate 0 pair = _
  exact positiveResidualLimitP286AuxiliaryCoordinate_apply 0 pair

theorem canonicalP286Generator_coordinatePairing_self :
    p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateEquiv canonicalP286Generator) = 5 := by
  simp only [p286CoordinateLiePairing,
    p286CoordinateEquiv.symm_apply_apply]
  norm_num [p286LiePairing, specialUnitaryLiePairing,
    hyperchargeLiePairing, canonicalP286Generator,
    colorCartanGenerator, colorCartanRaw,
    weakCartanGenerator, weakCartanRaw, hyperchargeGenerator,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three,
    Fin.sum_univ_two] ; simp ; norm_num

theorem referenceP286HodgeCurvature_apply (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge
        referenceP286CurvatureCoordinate pair =
      if pair = 3 then
        -(1 / 4 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp_rw [referenceP286CurvatureCoordinate_apply]
  fin_cases pair <;>
    simp [lorentzianCoframeHodge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val]

theorem referenceP286HodgeAuxiliary_apply (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge
        referenceP286AuxiliaryCoordinate pair =
      if pair = 0 then
        (1 / 2 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp_rw [referenceP286AuxiliaryCoordinate_apply]
  fin_cases pair <;>
    simp [lorentzianCoframeHodge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val]

theorem referenceP286CoupledHodgeAuxiliary_eq_curvature :
    liftGaugeTwoFormOperator
        ((1 / 2 : ℝ) • lorentzianCoframeHodge)
        referenceP286AuxiliaryCoordinate =
      referenceP286CurvatureCoordinate := by
  funext pair
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp_rw [referenceP286AuxiliaryCoordinate_apply,
    referenceP286CurvatureCoordinate_apply]
  fin_cases pair <;>
    simp [lorentzianCoframeHodge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val] ;
    ring

theorem liftGaugeTwoFormOperator_id_p286
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form = form := by
  funext output
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp

theorem referenceP286MetricPairing_aux_hodgeCurvature :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
        (1 : LorentzianCoframe)
        referenceP286AuxiliaryCoordinate
        (liftGaugeTwoFormOperator lorentzianCoframeHodge
          referenceP286CurvatureCoordinate) = -(5 / 8 : ℝ) := by
  unfold generatedGaugeTwoFormMetricPairing
  simp_rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286,
    referenceP286AuxiliaryCoordinate_apply,
    referenceP286HodgeCurvature_apply]
  rw [Fin.sum_univ_six]
  simp [lorentzianTwoFormSign, pairFirst, pairSecond,
    minkowskiInternalSign, p286CoordinateLiePairing_smul_left,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val]
  rw [show
      -((4 : ℝ)⁻¹ • p286CoordinateEquiv canonicalP286Generator) =
          (-(4 : ℝ)⁻¹) • p286CoordinateEquiv canonicalP286Generator by
        rw [neg_smul],
    p286CoordinateLiePairing_smul_right,
    canonicalP286Generator_coordinatePairing_self]
  norm_num

theorem referenceP286GaugeBFDensity_eq_neg_five_sixteenths :
    generatedGaugeSectorBFDensity p286CoordinateLiePairing
        (1 : LorentzianCoframe) lorentzianCoframeHodge
        ((1 / 2 : ℝ) • lorentzianCoframeHodge)
        referenceP286CurvatureCoordinate
        referenceP286AuxiliaryCoordinate = -(5 / 16 : ℝ) := by
  unfold generatedGaugeSectorBFDensity
  rw [referenceP286CoupledHodgeAuxiliary_eq_curvature,
    referenceP286MetricPairing_aux_hodgeCurvature]
  ring

/-! ## Canonical uniform coframe direction -/

def radialCoframe (scalar : ℝ) : LorentzianCoframe :=
  scalar • (1 : LorentzianCoframe)

theorem coframeTwoFormLinear_smul
    (scalar : ℝ) (coframe : LorentzianCoframe) :
    coframeTwoFormLinear (scalar • coframe) =
      scalar ^ 2 • coframeTwoFormLinear coframe := by
  apply LinearMap.ext
  intro form
  funext output
  change (∑ input : Fin 6,
      coframeWedge (scalar • coframe) output input * form input) =
    scalar ^ 2 *
      ∑ input : Fin 6, coframeWedge coframe output input * form input
  rw [coframeWedge_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  ring

theorem radialCoframe_inv (scalar : ℝ) (nonzero : scalar ≠ 0) :
    (radialCoframe scalar)⁻¹ = scalar⁻¹ • (1 : LorentzianCoframe) := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [radialCoframe, Matrix.mul_apply, Matrix.one_apply, nonzero]

theorem radialCoframe_spacetimeHodge
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeGaugeSpacetimeHodgeLinear (radialCoframe scalar) =
      lorentzianCoframeHodgeEquiv.toLinearMap := by
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [radialCoframe_inv scalar nonzero]
  simp only [radialCoframe]
  rw [
    coframeTwoFormLinear_smul, coframeTwoFormLinear_smul,
    coframeTwoFormLinear_one]
  apply LinearMap.ext
  intro form
  funext output
  simp [LinearMap.comp_apply, nonzero]

theorem gravitySpacetimeHodge_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0)
    (bivector : PhysicalBivector) :
    gravitySpacetimeHodge (radialCoframe scalar) bivector =
      gravitySpacetimeHodge (1 : LorentzianCoframe) bivector := by
  funext internalPair
  unfold gravitySpacetimeHodge
  rw [radialCoframe_spacetimeHodge scalar nonzero,
    coframeGaugeSpacetimeHodgeLinear_one]

theorem gaugeOperatorCoefficient_smul
    (scalar : ℝ) (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (output input : Fin 6) :
    gaugeOperatorCoefficient (scalar • operator) output input =
      scalar * gaugeOperatorCoefficient operator output input := by
  unfold gaugeOperatorCoefficient
  rfl

theorem liftGaugeTwoFormOperator_smul_operator
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (scalar : ℝ) (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → V) :
    liftGaugeTwoFormOperator (scalar • operator) form =
      scalar • liftGaugeTwoFormOperator operator form := by
  funext output
  unfold liftGaugeTwoFormOperator
  simp_rw [gaugeOperatorCoefficient_smul]
  change (∑ input : Fin 6,
      (scalar * gaugeOperatorCoefficient operator output input) • form input) =
    scalar • ∑ input : Fin 6,
      gaugeOperatorCoefficient operator output input • form input
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [mul_smul]

theorem p286MetricPairing_radial
    (scalar : ℝ) (first second : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
        (radialCoframe scalar) first second =
      scalar ^ 4 *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
          (1 : LorentzianCoframe) first second := by
  unfold generatedGaugeTwoFormMetricPairing
  simp only [radialCoframe, coframeTwoFormLinear_smul,
    coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_smul_operator,
    liftGaugeTwoFormOperator_id_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem referenceP286GaugeBFDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedGaugeSectorBFDensity p286CoordinateLiePairing
        (radialCoframe scalar)
        (coframeGaugeSpacetimeHodgeLinear (radialCoframe scalar))
        ((1 / 2 : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (radialCoframe scalar))
        referenceP286CurvatureCoordinate
        referenceP286AuxiliaryCoordinate =
      scalar ^ 4 * (-(5 / 16 : ℝ)) := by
  rw [radialCoframe_spacetimeHodge scalar nonzero]
  have hodgeEq :
      lorentzianCoframeHodgeEquiv.toLinearMap =
        lorentzianCoframeHodge := rfl
  rw [hodgeEq]
  unfold generatedGaugeSectorBFDensity
  rw [p286MetricPairing_radial, p286MetricPairing_radial]
  have reference :=
    referenceP286GaugeBFDensity_eq_neg_five_sixteenths
  unfold generatedGaugeSectorBFDensity at reference
  linear_combination scalar ^ 4 * reference

theorem referenceOriginField_radial_volume (scalar : ℝ) :
    generatedVolumeDensity
        (withCoframe referenceOriginField (radialCoframe scalar)) =
      scalar ^ 4 := by
  unfold generatedVolumeDensity
  change abs (Matrix.det (scalar • (1 : LorentzianCoframe))) = scalar ^ 4
  rw [Matrix.det_smul]
  norm_num
  rw [← abs_pow]
  exact abs_of_nonneg (by positivity)

theorem coframeTwoFormMetricPairing_radial
    (scalar : ℝ) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing (radialCoframe scalar) first second =
      scalar ^ 4 *
        coframeTwoFormMetricPairing (1 : LorentzianCoframe) first second := by
  unfold coframeTwoFormMetricPairing
  simp only [radialCoframe, coframeTwoFormLinear_smul,
    coframeTwoFormLinear_one, LinearMap.smul_apply, LinearMap.id_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem gravityCoframePairing_radial
    (scalar : ℝ) (first second : PhysicalBivector) :
    gravityCoframePairing (radialCoframe scalar) first second =
      scalar ^ 4 *
        gravityCoframePairing (1 : LorentzianCoframe) first second := by
  unfold gravityCoframePairing
  simp_rw [coframeTwoFormMetricPairing_radial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  ring

theorem referenceOriginField_gravityBFDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedGravityBFDensity
        (withCoframe referenceOriginField (radialCoframe scalar)) =
      scalar ^ 4 * (-3 : ℝ) := by
  unfold generatedGravityBFDensity
  simp only [withCoframe]
  rw [gravitySpacetimeHodge_radial scalar nonzero,
    gravitySpacetimeHodge_radial scalar nonzero]
  rw [gravityCoframePairing_radial, gravityCoframePairing_radial]
  have reference := referenceOriginField_gravityBFDensity_eq_neg_three
  unfold generatedGravityBFDensity at reference
  rw [referenceOriginField_coframe_eq_one] at reference
  linear_combination scalar ^ 4 * reference

theorem referenceOriginField_simplicityDensity_withCoframe_zero
    (coframe : LorentzianCoframe) :
    generatedGravitySimplicityDensity
        (withCoframe referenceOriginField coframe) = 0 := by
  apply generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero
  exact referencePointField_multiplier_zero

theorem positiveSource_generatedGaugeCoupling_eq_half :
    (((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared :
      ℝ)) = 1 / 2 := by
  change positiveSmoothUnifiedSource.legacy.sigma = 1 / 2
  exact positiveSmoothUnifiedSource_legacy_sigma_eq_half

theorem referenceOriginField_gravitySectorLocalDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeGravitySectorLocalDensity referenceOriginField
        (radialCoframe scalar) =
      scalar ^ 8 * (-3 : ℝ) := by
  unfold coframeGravitySectorLocalDensity
  rw [referenceOriginField_radial_volume,
    referenceOriginField_simplicityDensity_withCoframe_zero,
    referenceOriginField_gravityBFDensity_radial scalar nonzero]
  ring

theorem referenceOriginField_gaugeSectorLocalDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField (radialCoframe scalar) =
      scalar ^ 8 * (-(5 / 16 : ℝ)) := by
  unfold coframeGaugeSectorLocalDensity
  dsimp only
  have couplingStrongWeak :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared := rfl
  have couplingStrongHypercharge :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared := rfl
  rw [← couplingStrongWeak, ← couplingStrongHypercharge]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  rw [positiveSource_generatedGaugeCoupling_eq_half]
  change generatedVolumeDensity
        (withCoframe referenceOriginField (radialCoframe scalar)) *
      generatedGaugeSectorBFDensity p286CoordinateLiePairing
        (radialCoframe scalar)
        (coframeGaugeSpacetimeHodgeLinear (radialCoframe scalar))
        ((1 / 2 : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (radialCoframe scalar))
        referenceP286CurvatureCoordinate
        referenceP286AuxiliaryCoordinate = _
  rw [referenceOriginField_radial_volume,
    referenceP286GaugeBFDensity_radial scalar nonzero]
  ring

theorem referenceOriginField_scalarCovariantDerivative_zero :
    referenceOriginField.scalarCovariantDerivative = 0 := by
  funext direction
  change holonomicScalarCovariantDerivative
      residualLimitLorentzCarrierReader 0 direction = 0
  rw [jointAuditReference_scalarCovariantDerivative_eq_carrier,
    positiveResidualLimitScalarCovariantDerivative_origin_eq_zero]

theorem referenceOriginField_scalar_eq_localVacuum :
    referenceOriginField.scalar =
      generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0 := by
  rfl

theorem referenceOriginField_scalarKinetic_withCoframe_zero
    (coframe : LorentzianCoframe) :
    generatedScalarKineticDensity positiveSmoothUnifiedSource 0 0
        (withCoframe referenceOriginField coframe) = 0 := by
  unfold generatedScalarKineticDensity
  simp only [withCoframe]
  rw [referenceOriginField_scalarCovariantDerivative_zero]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

theorem referenceOriginField_scalarPotential_zero :
    generatedScalarPotential positiveSmoothUnifiedSource 0 0
        referenceOriginField.scalar = 0 := by
  rw [referenceOriginField_scalar_eq_localVacuum]
  exact generatedScalarPotential_localVacuum
    positiveSmoothUnifiedSource 0 0

theorem referenceOriginField_scalarSectorLocalDensity_zero
    (coframe : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField coframe = 0 := by
  unfold coframeScalarSectorLocalDensity
  rw [referenceOriginField_scalarKinetic_withCoframe_zero,
    referenceOriginField_scalarPotential_zero]
  ring

theorem referenceOriginField_matterSectorLocalDensity_zero
    (coframe : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField coframe = 0 := by
  unfold coframeMatterSectorLocalDensity generatedContinuumMatterDensity
  change generatedVolumeDensity (withCoframe referenceOriginField coframe) *
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 0 0
      (generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe referenceOriginField coframe))).re = 0
  simp [matterDualFrameRelative]

/-! ## Actual four-sector normal form and radial coframe response -/

theorem referenceOriginField_scalarSectorStressCovector_zero :
    coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField = 0 := by
  unfold coframeScalarSectorStressCovector
  have densityZero :
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          referenceOriginField = 0 := by
    funext coframe
    exact referenceOriginField_scalarSectorLocalDensity_zero coframe
  rw [densityZero]
  simp

theorem referenceOriginField_matterSectorStressCovector_zero :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField = 0 := by
  unfold coframeMatterSectorStressCovector
  have densityZero :
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          referenceOriginField = 0 := by
    funext coframe
    exact referenceOriginField_matterSectorLocalDensity_zero coframe
  rw [densityZero]
  simp

theorem referenceOriginField_coframeStress_fourSectorNormalForm :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField =
      coframeGravitySectorStressCovector referenceOriginField +
        coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
          referenceOriginField +
        coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
          referenceOriginField +
        coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
          referenceOriginField := by
  apply coframeLocalStressCovector_eq_sector_sum
  rw [referenceOriginField_coframe_eq_one]
  simp

theorem referenceOriginField_coframeStress_gravityGaugeNormalForm :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField =
      coframeGravitySectorStressCovector referenceOriginField +
        coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
          referenceOriginField := by
  rw [referenceOriginField_coframeStress_fourSectorNormalForm,
    referenceOriginField_scalarSectorStressCovector_zero,
    referenceOriginField_matterSectorStressCovector_zero]
  simp

theorem referenceOriginField_coframeLocalDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeLocalDensity positiveSmoothUnifiedSource 0 referenceOriginField
        (radialCoframe scalar) =
      -(53 / 16 : ℝ) * scalar ^ 8 := by
  rw [coframeLocalDensity_eq_sector_sum,
    referenceOriginField_gravitySectorLocalDensity_radial scalar nonzero,
    referenceOriginField_gaugeSectorLocalDensity_radial scalar nonzero,
    referenceOriginField_scalarSectorLocalDensity_zero,
    referenceOriginField_matterSectorLocalDensity_zero]
  ring

theorem referenceOriginField_coframeStress_identity_eq_neg_fiftyThree_halves :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField (1 : LorentzianCoframe) =
      -(53 / 2 : ℝ) := by
  have nondegenerate : Matrix.det referenceOriginField.coframe ≠ 0 := by
    rw [referenceOriginField_coframe_eq_one]
    simp
  have outer := coframeLocalDensity_hasFDerivAt
    positiveSmoothUnifiedSource 0 referenceOriginField nondegenerate
  have identityDerivative := hasDerivAt_id (x := (1 : ℝ))
  have radialDerivative := identityDerivative.smul_const
    (1 : LorentzianCoframe)
  have radialDerivativeValue :
      (1 : ℝ) • (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) := by
    simp
  have radialDerivativeAtOne :=
    radialDerivative.congr_deriv radialDerivativeValue
  have pointEquality :
      referenceOriginField.coframe = radialCoframe (1 : ℝ) := by
    rw [referenceOriginField_coframe_eq_one]
    simp [radialCoframe]
  have composed := outer.comp_hasDerivAt_of_eq (1 : ℝ)
    radialDerivativeAtOne pointEquality
  have polynomial := (identityDerivative.pow 8).const_mul
    (-(53 / 16 : ℝ))
  have formulaEventually : Filter.EventuallyEq (nhds (1 : ℝ))
      (fun scalar : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0
          referenceOriginField (radialCoframe scalar))
      (fun scalar : ℝ => -(53 / 16 : ℝ) * scalar ^ 8) := by
    filter_upwards [eventually_ne_nhds
        (one_ne_zero : (1 : ℝ) ≠ 0)] with scalar nonzero
    exact referenceOriginField_coframeLocalDensity_radial scalar nonzero
  have exactDerivative := polynomial.congr_of_eventuallyEq formulaEventually
  have derivativeEquality := composed.unique exactDerivative
  norm_num at derivativeEquality
  exact derivativeEquality

theorem referenceOriginField_coframeStress_ne_zero :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField ≠ 0 := by
  intro zeroStress
  have evaluated := congrArg
    (fun stress : LorentzianCoframe →L[ℝ] ℝ =>
      stress (1 : LorentzianCoframe)) zeroStress
  rw [referenceOriginField_coframeStress_identity_eq_neg_fiftyThree_halves]
    at evaluated
  norm_num at evaluated

theorem qDReader_coframeResidual_origin_ne_zero :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField qDReader 0) ≠ 0 := by
  rw [qDReader_pointField_origin_eq_reference]
  exact referenceOriginField_coframeStress_ne_zero

/-- The stored multiplier is literally zero.  Consequently the squared
simplicity sector and its coframe derivative vanish; no multiplier is tuned. -/
theorem referencePointField_zeroMultiplier_simplicityResponse :
    fderiv ℝ
        (fun candidate : LorentzianCoframe =>
          generatedGravitySimplicityDensity
            (withCoframe
              (toContinuumPointField residualLimitLorentzCarrierReader 0)
              candidate))
        (toContinuumPointField residualLimitLorentzCarrierReader 0).coframe = 0 :=
  zeroMultiplier_withCoframe_fderiv_eq_zero
    (toContinuumPointField residualLimitLorentzCarrierReader 0)

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitCoframeBalanceDecision
