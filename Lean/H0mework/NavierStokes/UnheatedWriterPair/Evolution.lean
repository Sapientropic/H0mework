import H0mework.NavierStokes.StressDynamics.ConvectionFlux
import H0mework.NavierStokes.StressResolvent.SourceResolvent
import H0mework.NavierStokes.WindowPhysics.WindowJets

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedStressPairEvolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeSourceResolvent NativeRawStressAction
open NativeCommonAdvectorAction NativeHigherTimeJets NativeConvectionFlux NativeForwardWindowJets
noncomputable section
variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def nonlinear (source : StressAt escape) (index : ℕ) (time : ℝ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave ∈ modes source index then
    transverseProjectionCLM wave (convectionCLM (modes source index) ((stage source index).trajectory time) wave (rawField source index time)) else 0

theorem field_supported (source : StressAt escape) (index : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1)
    (wave : IntegerWavevector) (outside : wave ∉ modes source index) : rawField source index time wave = 0 := by
  rw [rawField, NativeRecoveryTimeGramAction.biotSavartCLM_apply, wholeBiotSavartVelocityState_apply,
    finiteStateVelocityCoefficient, ((stage source index).physical time inside).2.1 wave outside]
  simp [biotSavartVelocityCoefficient]

theorem field_transverse (source : StressAt escape) (index : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    complexWavevector wave ⬝ᵥ rawField source index time wave = 0 := by
  rw [rawField, NativeRecoveryTimeGramAction.biotSavartCLM_apply, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient]
  exact complexWavevector_dot_biotSavartVelocityCoefficient wave _

theorem rate_split (source : StressAt escape) (index : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1)
    (wave : IntegerWavevector) :
    rawRate source index time wave = nonlinear source index time wave -
      (nu.coeff * integerWaveViscousMultiplier wave) • rawField source index time wave := by
  rw [← source_diagonal source index time inside, sourceOperator, operator_apply]
  change (if wave ∈ modes source index then transverseProjection wave
    (convectionCLM (modes source index) ((stage source index).trajectory time) wave (rawField source index time) -
      (nu.coeff * integerWaveViscousMultiplier wave) • rawField source index time wave) else 0) = _
  by_cases member : wave ∈ modes source index
  · rw [if_pos member, nonlinear, if_pos member]
    change (transverseProjectionCLM wave) (convectionCLM (modes source index) ((stage source index).trajectory time) wave
      (rawField source index time) - (nu.coeff * integerWaveViscousMultiplier wave) • rawField source index time wave) = _
    rw [map_sub, map_smul]
    simp only [transverseProjectionCLM_apply]
    rw [transverseProjection_eq_self_of_transverse (fun zero => modes_zero source index (zero ▸ member))
      (field_transverse source index time wave)]
  · simp only [nonlinear, if_neg member, field_supported source index time inside wave member, smul_zero, sub_self]

theorem nonlinear_original (source : StressAt escape) (index : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1)
    (wave : IntegerWavevector) : nonlinear source index time wave =
      if wave ∈ modes source index then NativeTimeJetCarrier.projectedDivergenceCLM wave
        (mixedFlux (rawField source index time) (rawField source index time) wave) else 0 := by
  unfold nonlinear
  split_ifs
  · have supported : ∀ wave ∉ modes source index, (stage source index).trajectory time wave = 0 :=
      ((stage source index).physical time inside).2.1
    rw [finite_convection (modes source index) _ _ supported
      (field_supported source index time inside) wave, ← mixed_divergence _ _ (wholeBiotSavartVelocityState_transverse _)]
    simp only [rawField, NativeRecoveryTimeGramAction.biotSavartCLM_apply]
    rfl
  · rfl

def decay (nu : Viscosity) (first last : IntegerWavevector) : ℝ :=
  nu.coeff * (integerWaveViscousMultiplier first + integerWaveViscousMultiplier last)

def pair (source : StressAt escape) (index : ℕ) (first last : IntegerWavevector) (output input : Coordinate) (time : ℝ) : ℂ :=
  -(rawField source index time first input * rawField source index time last output)

def triple (source : StressAt escape) (index : ℕ) (first last : IntegerWavevector) (output input : Coordinate) (time : ℝ) : ℂ :=
  -(nonlinear source index time first input * rawField source index time last output +
    rawField source index time first input * nonlinear source index time last output)

theorem pair_hasDerivAt (source : StressAt escape) (index : ℕ) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (pair source index first last output input)
      (triple source index first last output input time - decay nu first last • pair source index first last output input time) time := by
  have row (wave : IntegerWavevector) (coordinate : Coordinate) :=
    ((ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).comp (evaluation wave)).hasFDerivAt.comp_hasDerivAt time
      (rawField_hasDerivAt source index time inside)
  have actual := ((row first input).mul (row last output)).neg
  convert! actual using 1
  change _ = -(rawRate source index time first input * rawField source index time last output +
    rawField source index time first input * rawRate source index time last output)
  rw [rate_split source index time inside first, rate_split source index time inside last]
  simp only [triple, pair, decay, Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
  push_cast
  ring

theorem pair_stress (source : StressAt escape) (index : ℕ) (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    NativeCompleteStressCarrier.read (rawStress source index time) wave output input =
      ∑' first, pair source index first (wave-first) output input time := by
  rw [rawStress, NativeCompleteStressBilinear.mixed_read]
  simp only [pair, mixedFlux, tsum_neg]

theorem pair_continuousOn (source : StressAt escape) (index : ℕ) (first last : IntegerWavevector) (output input : Coordinate) :
    ContinuousOn (pair source index first last output input) (Icc (0 : ℝ) 1) :=
  fun time inside => (pair_hasDerivAt source index first last output input time inside).continuousAt.continuousWithinAt

theorem nonlinear_continuousOn (source : StressAt escape) (index : ℕ) (wave : IntegerWavevector) :
    ContinuousOn (fun time => nonlinear source index time wave) (Icc (0 : ℝ) 1) := by
  have rate := (evaluation wave).continuous.comp_continuousOn (rawRate_continuousOn source index)
  have field := (evaluation wave).continuous.comp_continuousOn
    (fun time inside => (rawField_hasDerivAt source index time inside).continuousAt.continuousWithinAt)
  apply (rate.add (field.const_smul (nu.coeff * integerWaveViscousMultiplier wave))).congr
  intro time inside
  have same := rate_split source index time inside wave
  change nonlinear source index time wave = rawRate source index time wave +
    (nu.coeff * integerWaveViscousMultiplier wave) • rawField source index time wave
  rw [same]
  abel

theorem triple_continuousOn (source : StressAt escape) (index : ℕ) (first last : IntegerWavevector) (output input : Coordinate) :
    ContinuousOn (triple source index first last output input) (Icc (0 : ℝ) 1) := by
  have field := fun wave coordinate => (ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).continuous.comp_continuousOn
    ((evaluation wave).continuous.comp_continuousOn (fun time inside => (rawField_hasDerivAt source index time inside).continuousAt.continuousWithinAt))
  have action := fun wave coordinate => (ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).continuous.comp_continuousOn
    (nonlinear_continuousOn source index wave)
  exact ((action first input |>.mul (field last output)).add ((field first input).mul (action last output))).neg


def kernelWeight (order : ℕ) (observation clockOrigin : ℝ) (time : ℝ) : ℝ :=
  kernelJet order (observation - (clockOrigin + time))

theorem kernelWeight_hasDerivAt (order : ℕ) (observation clockOrigin time : ℝ) :
    HasDerivAt (kernelWeight order observation clockOrigin) (-kernelWeight (order+1) observation clockOrigin time) time := by
  have generated : HasDerivAt (kernelJet order) (kernelJet (order+1) (observation-(clockOrigin+time)))
      (observation-(clockOrigin+time)) := by
    have actual := ((kernelJet_smooth order).differentiable (by simp) (observation-(clockOrigin+time))).hasDerivAt
    simpa only [kernelJet, iteratedDeriv_succ] using actual
  have actual := generated.comp time (((hasDerivAt_id time).const_add clockOrigin).const_sub observation)
  simpa only [mul_neg_one, one_mul, Function.comp_def, id_eq, kernelWeight] using! actual

theorem kernelWeight_continuous (order : ℕ) (observation clockOrigin : ℝ) :
    Continuous (kernelWeight order observation clockOrigin) :=
  (kernelJet_smooth order).continuous.comp (continuous_const.sub (continuous_const.add continuous_id))

theorem weighted_pair_hasDerivAt (source : StressAt escape) (index order : ℕ) (first last : IntegerWavevector)
    (output input : Coordinate) (observation clockOrigin time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun sample => kernelWeight order observation clockOrigin sample • pair source index first last output input sample)
      (kernelWeight order observation clockOrigin time • triple source index first last output input time -
        kernelWeight (order+1) observation clockOrigin time • pair source index first last output input time -
        decay nu first last • (kernelWeight order observation clockOrigin time • pair source index first last output input time)) time := by
  have actual := (kernelWeight_hasDerivAt order observation clockOrigin time).smul
    (pair_hasDerivAt source index first last output input time inside)
  convert! actual using 1
  simp only [smul_sub, neg_smul, Complex.real_smul]
  ring

theorem weighted_pair_integral (source : StressAt escape) (index order : ℕ) (first last : IntegerWavevector)
    (output input : Coordinate) (observation clockOrigin : ℝ) (start finish : Icc (0 : ℝ) 1) :
    decay nu first last • (∫ time in start.1..finish.1,
      kernelWeight order observation clockOrigin time • pair source index first last output input time) =
      (∫ time in start.1..finish.1, kernelWeight order observation clockOrigin time • triple source index first last output input time) -
      (∫ time in start.1..finish.1, kernelWeight (order+1) observation clockOrigin time • pair source index first last output input time) -
      (kernelWeight order observation clockOrigin finish.1 • pair source index first last output input finish.1 -
        kernelWeight order observation clockOrigin start.1 • pair source index first last output input start.1) := by
  have subset := uIcc_subset_Icc start.2 finish.2
  have quadratic (n : ℕ) : IntervalIntegrable (fun time => kernelWeight n observation clockOrigin time •
      pair source index first last output input time) volume start.1 finish.1 :=
    ((kernelWeight_continuous n observation clockOrigin).continuousOn.smul
      (pair_continuousOn source index first last output input)).mono subset |>.intervalIntegrable
  have cubic : IntervalIntegrable (fun time => kernelWeight order observation clockOrigin time •
      triple source index first last output input time) volume start.1 finish.1 :=
    ((kernelWeight_continuous order observation clockOrigin).continuousOn.smul
      (triple_continuousOn source index first last output input)).mono subset |>.intervalIntegrable
  have scaled : IntervalIntegrable (fun time => decay nu first last •
      (kernelWeight order observation clockOrigin time • pair source index first last output input time)) volume start.1 finish.1 := by
    simpa only [Pi.smul_apply] using! (quadratic order).smul (decay nu first last)
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => weighted_pair_hasDerivAt source index order first last output input observation clockOrigin time (subset inside))
    ((cubic.sub (quadratic (order+1))).sub scaled)
  rw [intervalIntegral.integral_sub (cubic.sub (quadratic (order+1))) scaled,
    intervalIntegral.integral_sub cubic (quadratic (order+1)), intervalIntegral.integral_smul] at written
  rw [sub_eq_iff_eq_add] at written
  rw [written]
  abel

theorem decay_positive (first last : IntegerWavevector) (nonzero : first ≠ 0 ∨ last ≠ 0) : 0 < decay nu first last := by
  apply mul_pos nu.coeff_pos
  have nonnegative (wave : IntegerWavevector) : 0 ≤ integerWaveViscousMultiplier wave :=
    mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
  have positive (wave : IntegerWavevector) (nonzero : wave ≠ 0) : 0 < integerWaveViscousMultiplier wave :=
    mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos nonzero)
  rcases nonzero with left | right
  · exact add_pos_of_pos_of_nonneg (positive first left) (nonnegative last)
  · exact add_pos_of_nonneg_of_pos (nonnegative first) (positive last right)

theorem output_decay (first last : IntegerWavevector) :
    nu.coeff * integerWaveViscousMultiplier (first+last) ≤ 2 * decay nu first last := by
  have row (coordinate : Coordinate) : ((first coordinate : ℝ) + (last coordinate : ℝ)) ^ 2 ≤
      2 * ((first coordinate : ℝ) ^ 2 + (last coordinate : ℝ) ^ 2) := by nlinarith [sq_nonneg ((first coordinate : ℝ) - (last coordinate : ℝ))]
  have sum := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun coordinate _ => row coordinate)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at sum
  unfold decay integerWaveViscousMultiplier integerWaveNormSq
  simp only [Pi.add_apply, Int.cast_add]
  have scaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left sum (sq_nonneg (2 * Real.pi))) nu.coeff_pos.le
  convert! scaled using 1
  ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedStressPairEvolution
