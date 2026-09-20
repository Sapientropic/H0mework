import H0mework.Physics.FinalJoint.FixedTimeAxisP286ResidualNormalForm

/-!
# Fixed final-common time-axis P286 live-Hodge normal form

This module expands pair zero of the live coframe Hodge on the literal
fixed P506/L0 final-common time-axis coframe.  It is a readout of that actual;
no residual coordinate, support choice, lower-order numerical value, or new
field is used to generate a successor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286LiveHodgeNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ResidualNormalForm
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLiftRegression

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private def spatialBlock (coframe : LorentzianCoframe) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun row column => coframe row.succ column.succ

private theorem inverse_timeRow_of_timeRow
    (coframe : LorentzianCoframe)
    (timeRow : ∀ column, coframe 0 column = (1 : LorentzianCoframe) 0 column)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (column : LorentzianIndex) :
    coframe⁻¹ 0 column = (1 : LorentzianCoframe) 0 column := by
  have determinantUnit : IsUnit (Matrix.det coframe) :=
    isUnit_iff_ne_zero.mpr nondegenerate
  have product := congrFun
    (congrFun (Matrix.mul_nonsing_inv coframe determinantUnit) 0) column
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at product
  rw [timeRow 0, timeRow 1, timeRow 2, timeRow 3] at product
  simpa [Matrix.one_apply] using product

private theorem inverse_spatialBlock_of_timeRow
    (coframe : LorentzianCoframe)
    (timeRow : ∀ column, coframe 0 column = (1 : LorentzianCoframe) 0 column)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    (spatialBlock coframe)⁻¹ = spatialBlock coframe⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have determinantUnit : IsUnit (Matrix.det coframe) :=
    isUnit_iff_ne_zero.mpr nondegenerate
  ext row column
  have product := congrFun
    (congrFun (Matrix.nonsing_inv_mul coframe determinantUnit)
      row.succ) column.succ
  fin_cases row <;> fin_cases column <;>
    simpa [spatialBlock, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, timeRow] using product

private theorem liveHodge_pairZero_block_normalForm
    (coframe : LorentzianCoframe)
    (timeRow : ∀ column, coframe 0 column = (1 : LorentzianCoframe) 0 column)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first third : ℝ) :
    coframeGaugeSpacetimeHodgeLinear coframe
        ![0, 0, 0, first, 0, third] 0 =
      let spatial := spatialBlock coframe
      spatial⁻¹ 0 0 *
          ((spatial 1 1 * spatial 2 2 - spatial 1 2 * spatial 2 1) * first +
            (spatial 1 0 * spatial 2 1 - spatial 1 1 * spatial 2 0) * third) +
        spatial⁻¹ 0 1 *
          ((spatial 2 1 * spatial 0 2 - spatial 2 2 * spatial 0 1) * first +
            (spatial 2 0 * spatial 0 1 - spatial 2 1 * spatial 0 0) * third) +
        spatial⁻¹ 0 2 *
          ((spatial 0 1 * spatial 1 2 - spatial 0 2 * spatial 1 1) * first +
            (spatial 0 0 * spatial 1 1 - spatial 0 1 * spatial 1 0) * third) := by
  have inverseRow := inverse_timeRow_of_timeRow
    coframe timeRow nondegenerate
  have inverseSpatial := inverse_spatialBlock_of_timeRow
    coframe timeRow nondegenerate
  have inverseSpatialEntry (row column : Fin 3) :
      coframe⁻¹ row.succ column.succ =
        (spatialBlock coframe)⁻¹ row column := by
    exact congrFun (congrFun inverseSpatial row) column |>.symm
  have inverse11 :
      coframe⁻¹ 1 1 = (spatialBlock coframe)⁻¹ 0 0 := by
    simpa using inverseSpatialEntry 0 0
  have inverse12 :
      coframe⁻¹ 1 2 = (spatialBlock coframe)⁻¹ 0 1 := by
    simpa using inverseSpatialEntry 0 1
  have inverse13 :
      coframe⁻¹ 1 3 = (spatialBlock coframe)⁻¹ 0 2 := by
    simpa using inverseSpatialEntry 0 2
  simp only [coframeGaugeSpacetimeHodgeLinear,
    LinearMap.comp_apply, inverseCoframeTwoFormLinear]
  unfold coframeTwoFormLinear
  simp only [Fin.sum_univ_six]
  simp [coframeWedge, pairFirst, pairSecond,
    EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv,
    lorentzianCoframeHodge, spatialBlock, inverseRow]
  rw [inverse11, inverse12, inverse13]

def fixedP506L0FinalCommonTimeAxisSpatialCoframeNormalForm
    (time : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + (time ^ 2 / 2) •
    fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian

theorem fixedP506L0FinalCommonTimeAxisSpatialCoframe_eq_normalForm
    (time : ℝ) :
    fixedP506L0FinalCommonTimeAxisSpatialCoframe 0 time =
      fixedP506L0FinalCommonTimeAxisSpatialCoframeNormalForm time := by
  exact
    fixedP506L0FinalCommonTimeAxisSpatialCoframe_eq_curvatureActionDefect time

def fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient
    (time : ℝ) : ℝ :=
  let spatial := fixedP506L0FinalCommonTimeAxisSpatialCoframeNormalForm time
  spatial⁻¹ 0 0 *
      ((spatial 1 1 * spatial 2 2 - spatial 1 2 * spatial 2 1) / 3 +
        time * (spatial 1 0 * spatial 2 1 - spatial 1 1 * spatial 2 0)) +
    spatial⁻¹ 0 1 *
      ((spatial 2 1 * spatial 0 2 - spatial 2 2 * spatial 0 1) / 3 +
        time * (spatial 2 0 * spatial 0 1 - spatial 2 1 * spatial 0 0)) +
    spatial⁻¹ 0 2 *
      ((spatial 0 1 * spatial 1 2 - spatial 0 2 * spatial 1 1) / 3 +
        time * (spatial 0 0 * spatial 1 1 - spatial 0 1 * spatial 1 0))

theorem finalCommon_liveHodge_timeAxis_pairZero_normalForm
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    coframeGaugeSpacetimeHodgeLinear
        ((fixedP506L0FinalCommonActionActual 0).coframe
          (canonicalCauchySlicePoint time 0))
        ![0, 0, 0, (1 / 3 : ℝ), 0, time] 0 =
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time := by
  let coframe :=
    (fixedP506L0FinalCommonActionActual 0).coframe
      (canonicalCauchySlicePoint time 0)
  have timeRow (column : LorentzianIndex) :
      coframe 0 column = (1 : LorentzianCoframe) 0 column := by
    exact fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow
      0 time column
  have nondegenerate : Matrix.det coframe ≠ 0 :=
    fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate 0 inDomain
  have block := liveHodge_pairZero_block_normalForm
    coframe timeRow nondegenerate (1 / 3) time
  have spatialEq :
      spatialBlock coframe =
        fixedP506L0FinalCommonTimeAxisSpatialCoframe 0 time := by
    rfl
  rw [spatialEq,
    fixedP506L0FinalCommonTimeAxisSpatialCoframe_eq_normalForm time] at block
  dsimp [coframe] at block
  unfold fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient
  dsimp only
  convert block using 1
  all_goals ring

theorem finalCommon_liveP286Hodge_timeAxis_pairZero_normalForm
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear
          ((fixedP506L0FinalCommonActionActual 0).coframe
            (canonicalCauchySlicePoint time 0)))
        ![0, 0, 0,
          (1 / 3 : ℝ) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
          0,
          time • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] 0 =
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  let charge :=
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge.ofLp internal
  have formEq :
      (fun input : Fin 6 =>
        (![0, 0, 0,
          (1 / 3 : ℝ) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
          0,
          time • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge]
          input).ofLp internal) =
        charge • ![0, 0, 0, (1 / 3 : ℝ), 0, time] := by
    funext input
    fin_cases input <;>
      simp [charge] <;> ring
  rw [formEq]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  change
    coframeGaugeSpacetimeHodgeLinear
        ((fixedP506L0FinalCommonActionActual 0).coframe
          (canonicalCauchySlicePoint time 0))
        (charge • ![0, 0, 0, (1 / 3 : ℝ), 0, time]) 0 =
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time * charge
  rw [map_smul, Pi.smul_apply,
    finalCommon_liveHodge_timeAxis_pairZero_normalForm time inDomain]
  ring

private theorem fixedSource_blockwiseCoupling_same
    (parameter : ℝ) (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear
        parameter parameter parameter coordinate =
      parameter • coordinate := by
  apply p286CoordinateEquiv.symm.injective
  simp [formNativeP286BlockwiseCouplingCoordinateLinear,
    formNativeP286BlockwiseCouplingActualLinear]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

private theorem fixedSource_blockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [fixedSource_blockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

theorem finalCommon_p286AuxiliaryResidual_timeAxis_pairZero_normalForm
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0FinalCommonActionActual 0)
        (canonicalCauchySlicePoint time 0)) 0 =
      c3h181StrongCouplingSquared •
        ((1 / 3 -
            fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
  have whole := congrFun
    (finalCommon_p286AuxiliaryResidualCoordinate_timeAxis_normalForm time) 0
  rw [fixedSource_blockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286] at whole
  simp only [Pi.sub_apply, Pi.smul_apply, Matrix.cons_val_zero] at whole
  rw [finalCommon_liveP286Hodge_timeAxis_pairZero_normalForm time inDomain]
    at whole
  calc
    _ = (c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge -
        (c3h181StrongCouplingSquared *
          fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
      simpa only [c3h181StrongCouplingSquared, smul_smul] using whole
    _ = _ := by
      module

theorem fixedP506L0FinalCommon_strongCouplingSquared_eq_half :
    c3h181StrongCouplingSquared = 1 / 2 := by
  change positiveSmoothUnifiedSource.legacy.sigma = (1 / 2 : ℝ)
  exact positiveSmoothUnifiedSource_legacy_sigma_eq_half

theorem finalCommon_p286AuxiliaryResidual_timeAxis_pairZero_eq_zero_iff
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain 0) :
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0FinalCommonActionActual 0)
        (canonicalCauchySlicePoint time 0)) 0 = 0 ↔
      fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time =
        1 / 3 := by
  rw [finalCommon_p286AuxiliaryResidual_timeAxis_pairZero_normalForm
    time inDomain]
  have couplingNonzero : c3h181StrongCouplingSquared ≠ 0 := by
    rw [fixedP506L0FinalCommon_strongCouplingSquared_eq_half]
    norm_num
  have chargeNonzero :
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge ≠ 0 :=
    c3h165_generatedGaussCharge_ne_zero_regression
  constructor
  · intro residualZero
    rw [smul_smul] at residualZero
    have scalarZero :
        c3h181StrongCouplingSquared *
            (1 / 3 -
              fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time) =
          0 :=
      (smul_eq_zero.mp residualZero).resolve_right chargeNonzero
    have differenceZero :
        1 / 3 -
            fixedP506L0FinalCommonTimeAxisLiveHodgePairZeroCoefficient time =
          0 :=
      (mul_eq_zero.mp scalarZero).resolve_left couplingNonzero
    linarith
  · intro coefficientEq
    rw [coefficientEq]
    norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286LiveHodgeNormalForm
