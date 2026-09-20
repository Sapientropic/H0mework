import H0mework.Physics.SpinPair.Adjoint
import H0mework.Physics.SpinPair.DiracActual

/-! The actual independent dual closes the original matter Euler equation.
Its generated temporal momentum derivative equals the full algebraic response. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineLorentzConnectionVariationDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open StageNineMatterPointwiseEquation StageNineDiracDualYukawaSpinJurisdiction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped ContDiff

noncomputable section

private theorem actual_algebraicKinetic
    (point : BasePoint) (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    actual.conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } direction)
        (holonomicMatterVariationAlgebraicDirection actual variation point direction)) =
      if direction = 0 then 0 else
        (-((spinScale-gaugeScale : ℝ) : ℂ) / 2) *
          spinPairDual (lowerDualPhase point) (upperDualPhase point) (matterCoordinateEquiv.symm variation) := by
  unfold holonomicMatterVariationAlgebraicDirection
  rw [actual_conjugateMatter, actual_coframe, actual_gravityConnection, actual_gaugeConnection,
    homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · have timeSpin : diracSpinConnectionLift (homogeneousConnection spinScale) 0 = 0 := by
      simp only [diracSpinConnectionLift, homogeneousConnection,
        loweredLorentzConnectionCoefficient_ofBivectorOneForm]
      simp [homogeneousContorsion, Fin.sum_univ_six]
    simp [timeSpin, gaugePotential, p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix, diracMatrixMatterAction_zero_matrix]
  · simp only [Fin.succ_ne_zero, ite_false, one_smul]
    have gauge : gaugePotential gaugeScale spatial.succ = gaugeScale • sourceColorP286Generator spatial := by
      fin_cases spatial <;> rfl
    rw [gauge]
    exact spinPairDual_spatialKinetic spinScale gaugeScale spatial _ _ _

theorem actual_matterAlgebraic
    (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource actual variation point =
      -frequency *
        (spinPairDual (lowerDualPhase point) (upperDualPhase point) (matterCoordinateEquiv.symm variation)).re := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField,
    map_add, actual_conjugateMatter, spinPairDual_yukawa_annihilates, add_zero]
  rw [Finset.smul_sum, map_sum]
  change |(actual.coframe point).det| * (∑ direction,
    actual.conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } direction)
        (holonomicMatterVariationAlgebraicDirection actual variation point direction))).re = _
  simp_rw [actual_algebraicKinetic]
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  simp [Fin.sum_univ_four, Complex.mul_re, frequency]
  ring

private theorem actual_dualEvaluation_differentiable
    (matter : DiracExteriorMatterCarrier) (point : BasePoint) :
    DifferentiableAt ℝ (fun candidate => actual.conjugateMatter candidate matter) point := by
  have upper : ContDiff ℝ ∞ upperDualPhase := contDiff_const.mul (phase_smooth frequency)
  have lower : ContDiff ℝ ∞ lowerDualPhase := contDiff_const.mul (phase_smooth (-frequency))
  have smooth : ContDiff ℝ ∞ (fun candidate => actual.conjugateMatter candidate matter) := by
    change ContDiff ℝ ∞ (fun candidate => ∑ spin, ∑ state,
      spinPairCoefficients (upperDualPhase candidate) (lowerDualPhase candidate) spin state *
        sourceColorDoubletDual state (matter spin))
    simp only [Fin.sum_univ_four, Fin.sum_univ_two, spinPairCoefficients,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_add, add_zero]
    fun_prop
  exact smooth.differentiable (by simp) |>.differentiableAt

private theorem actual_dualRealMomentum_derivative
    (matter : DiracExteriorMatterCarrier) (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (fun candidate => lapse * (actual.conjugateMatter candidate matter).re) point direction =
      lapse * (if direction = 0 then
        spinPairDual (Complex.I*(frequency : ℂ)*upperDualPhase point)
          (-Complex.I*(frequency : ℂ)*lowerDualPhase point) matter else 0).re := by
  have composed := ((lapse • Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt).comp point
    (actual_dualEvaluation_differentiable matter point).hasFDerivAt
  unfold fieldDirectionalDerivative
  rw [show (fun candidate => lapse * (actual.conjugateMatter candidate matter).re) =
    (lapse • Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ (fun candidate => actual.conjugateMatter candidate matter) by rfl,
    composed.fderiv]
  change lapse * (fieldDirectionalDerivative (fun candidate => actual.conjugateMatter candidate matter)
    point direction).re = _
  rw [actual_conjugateMatterDerivative]
  congr 2
  split_ifs
  · apply congrArg (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier => dual matter)
    congr 1 <;> ring
  · rfl

theorem actual_matterMomentum_derivative
    (point : BasePoint) (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (matterDifferentialMomentum positiveSmoothUnifiedSource actual variation direction) point direction =
      if direction = 0 then -frequency *
        (spinPairDual (lowerDualPhase point) (upperDualPhase point) (matterCoordinateEquiv.symm variation)).re
      else 0 := by
  have field : matterDifferentialMomentum positiveSmoothUnifiedSource actual variation direction =
      fun candidate => lapse * (actual.conjugateMatter candidate
        (Complex.I • diracMatrixMatterAction
          (inverseCoframeDiracGamma { coframe := homogeneousCoframe lapse, derivative := 0 } direction)
          (matterCoordinateEquiv.symm variation))).re := by
    funext candidate
    unfold matterDifferentialMomentum matterDifferentialVariationVector
    simp only [toContinuumPointField, actual_coframe]
    change |(homogeneousCoframe lapse).det| * _ = _
    rw [homogeneousCoframe_det, abs_of_pos lapse_pos]
  rw [field, actual_dualRealMomentum_derivative]
  by_cases time : direction = 0
  · subst direction
    rw [if_pos rfl, if_pos rfl, homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
    simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
    rw [smul_comm, map_smul, spinPairDual_temporalKinetic]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, zero_mul, sub_zero]
    simp only [zero_mul, neg_zero, sub_zero]
    field_simp [ne_of_gt lapse_pos]
  · simp [time]

theorem actual_matterEuler_zero
    (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource actual variation point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient matterDifferentialMomentumDivergence
  rw [actual_matterAlgebraic]
  simp only [actual_matterMomentum_derivative]
  simp

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
