import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.PrimitiveSource
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.CubicRaw

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadOutput
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTriadKernel NativeUnheatedTriadPrimitiveSource NativeUnheatedSourceGradient
open NativeWholeH1Mixed
noncomputable section
variable {nu : Viscosity}

theorem output_multiplier (a b c : IntegerWavevector) :
    integerWaveViscousMultiplier (a+b+c) ≤
      3*(integerWaveViscousMultiplier a+integerWaveViscousMultiplier b+integerWaveViscousMultiplier c) := by
  have coordinate (i : Coordinate) :
      ((a i : ℝ)+(b i : ℝ)+(c i : ℝ))^2 ≤ 3*((a i : ℝ)^2+(b i : ℝ)^2+(c i : ℝ)^2) := by
    nlinarith [sq_nonneg ((a i : ℝ)-(b i : ℝ)), sq_nonneg ((a i : ℝ)-(c i : ℝ)),
      sq_nonneg ((b i : ℝ)-(c i : ℝ))]
  have paid := Finset.sum_le_sum (s := Finset.univ) (fun i _ => coordinate i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at paid
  unfold integerWaveViscousMultiplier integerWaveNormSq
  simp only [Pi.add_apply, Int.cast_add]
  nlinarith [mul_le_mul_of_nonneg_left paid (sq_nonneg (2*Real.pi))]

theorem decay_coercivity (a b c : IntegerWavevector) :
    nu.coeff*integerWaveViscousMultiplier (a+b+c) ≤ 3*triadDecay nu a b c := by
  exact (mul_le_mul_of_nonneg_left (output_multiplier a b c) nu.coeff_pos.le).trans_eq (by
    unfold triadDecay
    ring)

theorem extract (a b c : IntegerWavevector) :
    integerWaveViscousMultiplier (a+b+c)*(triadDecay nu a b c)⁻¹ ≤ 3/nu.coeff := by
  have dominated : integerWaveViscousMultiplier (a+b+c) ≤ (3/nu.coeff)*triadDecay nu a b c := by
    have same : (3/nu.coeff)*triadDecay nu a b c =
        3*(integerWaveViscousMultiplier a+integerWaveViscousMultiplier b+integerWaveViscousMultiplier c) := by
      unfold triadDecay
      field_simp [nu.coeff_pos.ne']
    rw [same]
    exact output_multiplier a b c
  by_cases zero : triadDecay nu a b c = 0
  · simp only [zero, inv_zero, mul_zero]
    positivity [nu.coeff_pos]
  · exact (mul_le_mul_of_nonneg_right dominated (inv_nonneg.mpr (triad_nonnegative (nu := nu) a b c))).trans_eq
      (by rw [mul_assoc, mul_inv_cancel₀ zero, mul_one])

theorem extract_power (a b c : IntegerWavevector) (order : ℕ) :
    integerWaveViscousMultiplier (a+b+c)^order*(triadDecay nu a b c)⁻¹^order ≤ (3/nu.coeff)^order := by
  simpa only [mul_pow] using pow_le_pow_left₀
    (mul_nonneg (multiplier_nonnegative _) (inv_nonneg.mpr (triad_nonnegative (nu := nu) a b c)))
    (extract (nu := nu) a b c) order

theorem row_raw (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    NativeUnheatedTriadPrimitiveSource.row seed wave i j output spectator indices time =
      (triadDecay nu indices.2 (wave-indices.1-indices.2) indices.1)⁻¹ •
        NativeUnheatedCubicRaw.rawRow seed wave i j output spectator indices time := by
  rw [NativeUnheatedTriadPrimitiveSource.row_original]
  simp only [NativeUnheatedCubicRaw.rawRow, smul_smul]
  congr 1
  ring

theorem row_output_bound (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    integerWaveViscousMultiplier wave*‖NativeUnheatedTriadPrimitiveSource.row seed wave i j output spectator indices time‖ ≤
      (3/nu.coeff)*‖NativeUnheatedCubicRaw.rawRow seed wave i j output spectator indices time‖ := by
  rw [row_raw, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (triad_nonnegative (nu := nu) _ _ _)), ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have same : indices.2+(wave-indices.1-indices.2)+indices.1 = wave := by abel
  simpa only [same] using extract (nu := nu) indices.2 (wave-indices.1-indices.2) indices.1

theorem coefficient_output_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) :
    integerWaveViscousMultiplier wave*‖coefficient seed wave i j output spectator time‖ ≤
      (3/nu.coeff)*NativeUnheatedCubicRaw.coefficient seed*Real.sqrt (mass seed time) := by
  rw [coefficient_eq_tsum]
  calc
    _ ≤ integerWaveViscousMultiplier wave*(∑' indices, ‖NativeUnheatedTriadPrimitiveSource.row seed wave i j output spectator indices time‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (row_summable seed wave i j output spectator time)) (multiplier_nonnegative wave)
    _ ≤ (3/nu.coeff)*(∑' indices, ‖NativeUnheatedCubicRaw.rawRow seed wave i j output spectator indices time‖) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact Summable.tsum_le_tsum (fun indices => row_output_bound seed wave i j output spectator indices time)
        ((row_summable seed wave i j output spectator time).mul_left _)
        ((NativeUnheatedCubicRaw.absolute_summable seed time nonnegative regular wave i j output spectator).mul_left _)
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (NativeUnheatedCubicRaw.absolute_bound seed time nonnegative regular wave i j output spectator)
      (by positivity [nu.coeff_pos])).trans_eq (by ring)

def outputBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  18*(3/nu.coeff)*NativeUnheatedCubicRaw.coefficient seed

theorem outputBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ outputBudget seed := by
  unfold outputBudget
  positivity [nu.coeff_pos, NativeUnheatedCubicRaw.coefficient_nonnegative seed]

theorem primitive_output_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (output spectator : Coordinate) :
    integerWaveViscousMultiplier wave*‖primitive seed time wave output spectator‖ ≤
      outputBudget seed*Real.sqrt (mass seed time) := by
  rw [primitive, norm_neg]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (multiplier_nonnegative wave)).trans
  rw [Finset.mul_sum]
  have inner (i : Coordinate) :
      integerWaveViscousMultiplier wave*‖∑ j : Coordinate,
        (coefficient seed wave i j spectator output time+coefficient seed wave i j output spectator time)‖ ≤
          ∑ _j : Coordinate, ((3/nu.coeff)*NativeUnheatedCubicRaw.coefficient seed*Real.sqrt (mass seed time) +
            (3/nu.coeff)*NativeUnheatedCubicRaw.coefficient seed*Real.sqrt (mass seed time)) := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (multiplier_nonnegative wave)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (multiplier_nonnegative wave)).trans
    rw [mul_add]
    exact add_le_add (coefficient_output_bound seed time nonnegative regular wave i j spectator output)
      (coefficient_output_bound seed time nonnegative regular wave i j output spectator)
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
    inner i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at paid
  exact paid.trans_eq (by unfold outputBudget; ring)

theorem primitive_output_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave output spectator,
      integerWaveViscousMultiplier wave*‖primitive seed time wave output spectator‖ ≤
        outputBudget seed*Real.sqrt (mass seed time) := by
  filter_upwards [physical_H1_ae seed] with time paid nonnegative wave output spectator
  exact primitive_output_bound seed time nonnegative (paid nonnegative) wave output spectator

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadOutput
