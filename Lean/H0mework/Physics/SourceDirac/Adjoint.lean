import H0mework.Physics.SourceDirac.Forward

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineLorentzConnectionVariationDensity StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariationDensity
open StageNineMatterPointwiseEquation StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeJointResidualCarrier SU7MotherLieAlgebra SU7MotherGaugeTheory Gauge
open scoped ContDiff

noncomputable section

private theorem algebraic_kinetic (step : ℕ) (point : BasePoint)
    (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    (fieldAt step).conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } direction)
        (holonomicMatterVariationAlgebraicDirection (fieldAt step) variation point direction)) =
      if direction = 0 then 0 else
        (-((spinScale - gaugeScale : ℝ) : ℂ) / 2) *
          spinPairDual (lowerDual step point) (upperDual step point) (matterCoordinateEquiv.symm variation) := by
  unfold holonomicMatterVariationAlgebraicDirection
  rw [field_dual, field_coframe, field_gravityConnection, field_connection,
    homogeneousInverseGamma (clock step) (ne_of_gt (clock_pos step))]
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · simp [homogeneous_spin_time, gaugePotential, p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix]
  · simp only [Fin.succ_ne_zero, ite_false, one_smul]
    have gauge : gaugePotential gaugeScale spatial.succ = gaugeScale • sourceColorP286Generator spatial := by
      fin_cases spatial <;> rfl
    rw [gauge]
    exact spinPairDual_spatialKinetic spinScale gaugeScale spatial _ _ _

theorem matter_algebraic (step : ℕ) (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient (sourceAt step) (fieldAt step) variation point =
      -phaseRate step *
        (spinPairDual (lowerDual step point) (upperDual step point) (matterCoordinateEquiv.symm variation)).re := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField,
    map_add, field_dual, spinPairDual_yukawa_annihilates, add_zero]
  rw [Finset.smul_sum, map_sum]
  change |((fieldAt step).coframe point).det| * (∑ direction,
    (fieldAt step).conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } direction)
        (holonomicMatterVariationAlgebraicDirection (fieldAt step) variation point direction))).re = _
  simp_rw [algebraic_kinetic]
  rw [field_coframe, homogeneousCoframe_det, abs_of_pos (clock_pos step)]
  simp [Fin.sum_univ_four, Complex.mul_re, phaseRate]
  ring

private theorem dual_evaluation_differentiable (step : ℕ) (matter : DiracExteriorMatterCarrier) (point : BasePoint) :
    DifferentiableAt ℝ (fun candidate => (fieldAt step).conjugateMatter candidate matter) point := by
  have upperSmooth : ContDiff ℝ ∞ (upperDual step) := contDiff_const.mul (phase_smooth (phaseRate step))
  have lowerSmooth : ContDiff ℝ ∞ (lowerDual step) := contDiff_const.mul (phase_smooth (-phaseRate step))
  have smooth : ContDiff ℝ ∞ (fun candidate => (fieldAt step).conjugateMatter candidate matter) := by
    change ContDiff ℝ ∞ (fun candidate => ∑ spin, ∑ state,
      spinPairCoefficients (upperDual step candidate) (lowerDual step candidate) spin state *
        sourceColorDoubletDual state (matter spin))
    simp only [Fin.sum_univ_four, Fin.sum_univ_two, spinPairCoefficients,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_add, add_zero]
    fun_prop
  exact smooth.differentiable (by simp) |>.differentiableAt

private theorem dual_real_momentum_derivative (step : ℕ) (matter : DiracExteriorMatterCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (fun candidate => clock step * ((fieldAt step).conjugateMatter candidate matter).re) point direction =
      clock step * (if direction = 0 then spinPairDual
        (Complex.I * (phaseRate step : ℂ) * upperDual step point)
        (-Complex.I * (phaseRate step : ℂ) * lowerDual step point) matter else 0).re := by
  have composed := (((clock step) • Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt).comp point
    (dual_evaluation_differentiable step matter point).hasFDerivAt
  unfold fieldDirectionalDerivative
  rw [show (fun candidate => clock step * ((fieldAt step).conjugateMatter candidate matter).re) =
    ((clock step) • Complex.reCLM : ℂ →L[ℝ] ℝ) ∘
      (fun candidate => (fieldAt step).conjugateMatter candidate matter) by rfl, composed.fderiv]
  change clock step * (fieldDirectionalDerivative
    (fun candidate => (fieldAt step).conjugateMatter candidate matter) point direction).re = _
  rw [dual_derivative]
  congr 2
  split_ifs
  · apply congrArg (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier => dual matter)
    congr 1 <;> ring
  · rfl

theorem matter_momentum_derivative (step : ℕ) (point : BasePoint)
    (variation : MatterCoordinateCarrier) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (matterDifferentialMomentum (sourceAt step) (fieldAt step) variation direction) point direction =
      if direction = 0 then -phaseRate step *
        (spinPairDual (lowerDual step point) (upperDual step point) (matterCoordinateEquiv.symm variation)).re
      else 0 := by
  have field : matterDifferentialMomentum (sourceAt step) (fieldAt step) variation direction =
      fun candidate => clock step * ((fieldAt step).conjugateMatter candidate
        (Complex.I • diracMatrixMatterAction
          (inverseCoframeDiracGamma { coframe := homogeneousCoframe (clock step), derivative := 0 } direction)
          (matterCoordinateEquiv.symm variation))).re := by
    funext candidate
    unfold matterDifferentialMomentum matterDifferentialVariationVector
    simp only [toContinuumPointField, field_coframe]
    change |(homogeneousCoframe (clock step)).det| * _ = _
    rw [homogeneousCoframe_det, abs_of_pos (clock_pos step)]
  rw [field, dual_real_momentum_derivative]
  by_cases time : direction = 0
  · subst direction
    rw [if_pos rfl, if_pos rfl, homogeneousInverseGamma (clock step) (ne_of_gt (clock_pos step))]
    simp only [ite_true, coframeDiracMatrixMatterAction_smul_matrix]
    rw [smul_comm, map_smul, spinPairDual_temporalKinetic]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, zero_mul, sub_zero]
    simp only [zero_mul, neg_zero, sub_zero]
    field_simp [ne_of_gt (clock_pos step)]
  · simp [time]

theorem matter_directional_zero (step : ℕ) (point : BasePoint) (variation : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient (sourceAt step) (fieldAt step) variation point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient matterDifferentialMomentumDivergence
  rw [matter_algebraic]
  simp only [matter_momentum_derivative]
  simp

/-- Both complete current-epoch Dirac channels consume the same generated
Cartan/color operator and the actual source phase derivatives. -/
theorem dirac_channels_zero (step : ℕ) (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point
    residual.matter = 0 ∧ residual.conjugateMatter = 0 :=
  ⟨funext (matter_directional_zero step point), conjugate_channel_zero step point⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Dirac
