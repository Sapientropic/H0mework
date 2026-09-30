import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.HeatLimit

/-! The full nine-component stress loses its heat scale in every Fourier moment,
uniformly on the generated original time window. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTailStressLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowTailMoments NativeForwardWindowJets
open NativeCompleteStressCarrier NativeCompleteHeatTransport
noncomputable section
variable {nu : Viscosity}

def momentError (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (rank order : ℕ) (time : ℝ) (entry : Coordinate × Coordinate) : ℝ :=
  ∑' wave, frequencySize wave ^ order *
    ‖read (NativeWindowHeatEvolution.jet seed lag rank time).snd wave entry.1 entry.2 -
      read (jet seed rank time).snd wave entry.1 entry.2‖

theorem row_error (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (rank : ℕ) (time : ℝ) (wave : IntegerWavevector) (entry : Coordinate × Coordinate) :
    ‖read (NativeWindowHeatEvolution.jet seed lag rank time).snd wave entry.1 entry.2 -
      read (jet seed rank time).snd wave entry.1 entry.2‖ =
      (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) *
        ‖read (jet seed rank time).snd wave entry.1 entry.2‖ := by
  change ‖read (tensorHeat nu lag (jet seed rank time).snd) wave entry.1 entry.2 - _‖ = _
  rw [tensorHeat_read, Pi.smul_apply, Pi.smul_apply]
  have difference : finiteStateVorticityHeatMultiplier nu.coeff lag wave •
      read (jet seed rank time).snd wave entry.1 entry.2 -
        read (jet seed rank time).snd wave entry.1 entry.2 =
      (finiteStateVorticityHeatMultiplier nu.coeff lag wave - 1) •
        read (jet seed rank time).snd wave entry.1 entry.2 := by rw [sub_smul, one_smul]
  rw [difference, norm_smul]
  erw [Real.norm_eq_abs, abs_of_nonpos
    (sub_nonpos.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))]
  exact congrArg (fun scalar : ℝ => scalar * ‖read (jet seed rank time).snd wave entry.1 entry.2‖) (neg_sub _ _)

theorem momentError_bound (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (lag : ℝ≥0) (rank order : ℕ) (entry : Coordinate × Coordinate) :
    momentError seed lag rank order time entry ≤
      NativeHeatSpatialZero.errorBudget nu lag 0
        (fun wave => stressBudget seed horizon rank (order + 4) * decay wave) := by
  let bound := fun wave => stressBudget seed horizon rank (order + 4) * decay wave
  have nonnegative (wave : IntegerWavevector) : 0 ≤ bound wave := by
    dsimp only [bound, stressBudget, tailStressBudget]
    exact mul_nonneg (mul_nonneg (integral_nonneg fun shift => norm_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _)
  have decayBound (wave : IntegerWavevector) :
      frequencySize wave ^ order * ‖read (jet seed rank time).snd wave entry.1 entry.2‖ ≤ bound wave :=
    window_stress_decay seed horizon time inside rank order wave entry.1 entry.2
  have cap (wave : IntegerWavevector) :
      0 ≤ 1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave :=
    sub_nonneg.mpr (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave)
  have paid : Summable (fun wave => (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * bound wave) :=
    (decay_summable.mul_left _).of_nonneg_of_le (fun wave => mul_nonneg (cap wave) (nonnegative wave))
      (fun wave => mul_le_of_le_one_left (nonnegative wave)
        (sub_le_self 1 (finiteStateVorticityHeatMultiplier_nonneg _ _ _)))
  have point (wave : IntegerWavevector) :
      frequencySize wave ^ order *
        ‖read (NativeWindowHeatEvolution.jet seed lag rank time).snd wave entry.1 entry.2 -
          read (jet seed rank time).snd wave entry.1 entry.2‖ ≤
        (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) * bound wave := by
    rw [row_error]
    calc _ = (1 - finiteStateVorticityHeatMultiplier nu.coeff lag wave) *
          (frequencySize wave ^ order * ‖read (jet seed rank time).snd wave entry.1 entry.2‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (decayBound wave) (cap wave)
  simpa only [momentError, NativeHeatSpatialZero.errorBudget, pow_zero, one_mul] using
    (paid.of_nonneg_of_le (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (norm_nonneg _)) point).tsum_le_tsum point paid

theorem stress_moments_uniform_zero (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (rank order : ℕ) :
    TendstoUniformly (fun lag : ℝ≥0 => fun pair :
        Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon × (Coordinate × Coordinate) =>
      momentError seed lag rank order pair.1 pair.2) (fun _ => 0) (𝓝 0) := by
  have nonnegative (wave : IntegerWavevector) : 0 ≤ stressBudget seed horizon rank (order + 4) * decay wave := by
    dsimp only [stressBudget, tailStressBudget]
    exact mul_nonneg (mul_nonneg (integral_nonneg fun shift => norm_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _)
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  filter_upwards [(NativeHeatSpatialZero.errorBudget_zero nu 0
    (fun wave => stressBudget seed horizon rank (order + 4) * decay wave)
    (decay_summable.mul_left _) nonnegative).eventually (gt_mem_nhds positive)] with lag small
  intro pair
  have positiveError : 0 ≤ momentError seed lag rank order pair.1 pair.2 :=
    tsum_nonneg fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (norm_nonneg _)
  rw [dist_comm, dist_zero_right, Real.norm_of_nonneg positiveError]
  exact (momentError_bound seed horizon pair.1 pair.1.property lag rank order pair.2).trans_lt small

end
end SaturationMonoid.NavierStokes.NativeWindowTailStressLimit
