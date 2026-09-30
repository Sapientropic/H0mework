import H0mework.NavierStokes.UnifiedAction.UnifiedHeatAction
import H0mework.NavierStokes.SourceAction.Synthesis

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology

namespace SaturationMonoid.NavierStokes.NativeHeatSpatialMultiplier

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis

noncomputable section

theorem frequency_le (wave : IntegerWavevector) :
    frequencySize wave ≤ 4 + integerWaveNormSq wave := by
  have row (coordinate : Coordinate) :
      |(wave coordinate : ℝ)| ≤ 1 + (wave coordinate : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(wave coordinate : ℝ)| - 1), sq_abs (wave coordinate : ℝ)]
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun coordinate _ => row coordinate
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] at total
  unfold frequencySize integerWaveNormSq
  linarith

def heatScale (nu : Viscosity) (lag : ℝ≥0) : ℝ := nu.coeff * (2 * Real.pi) ^ 2 * lag

def budget (nu : Viscosity) (lag : ℝ≥0) (order : ℕ) : ℝ :=
  (order.factorial : ℝ) * Real.exp (4 * heatScale nu lag) / heatScale nu lag ^ order

theorem heatScale_pos (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) :
    0 < heatScale nu lag := by
  have : 0 < (lag : ℝ) := positive
  unfold heatScale
  positivity [nu.coeff_pos]

theorem budget_nonneg (nu : Viscosity) (lag : ℝ≥0) (order : ℕ) :
    0 ≤ budget nu lag order := by
  unfold budget heatScale
  positivity [nu.coeff_pos]

theorem multiplier_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave ^ order * finiteStateVorticityHeatMultiplier nu.coeff lag wave ≤
      budget nu lag order := by
  let a := heatScale nu lag
  let x := integerWaveNormSq wave
  have aPos : 0 < a := heatScale_pos nu lag positive
  have xNonneg : 0 ≤ x := integerWaveNormSq_nonneg wave
  have factorialPos : (0 : ℝ) < order.factorial := by positivity
  have polynomial := (div_le_iff₀ factorialPos).mp
    (Real.pow_div_factorial_le_exp (a * (4 + x)) (by positivity) order)
  have exponent : -(nu.coeff * integerWaveViscousMultiplier wave) * (lag : ℝ) = -(a * x) := by
    unfold a x heatScale integerWaveViscousMultiplier
    ring
  change frequencySize wave ^ order * Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (lag : ℝ)) ≤ _
  rw [exponent]
  calc
    _ ≤ (4 + x) ^ order * Real.exp (-(a * x)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (frequencySize_nonneg wave) (frequency_le wave) order)
        (Real.exp_pos _).le
    _ = ((a * (4 + x)) ^ order * Real.exp (-(a * x))) / a ^ order := by
      rw [mul_pow]
      field_simp
    _ ≤ (Real.exp (a * (4 + x)) * order.factorial * Real.exp (-(a * x))) / a ^ order :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right polynomial (Real.exp_pos _).le)
        (pow_nonneg aPos.le _)
    _ = budget nu lag order := by
      rw [mul_right_comm, ← Real.exp_add]
      have same : a * (4 + x) + -(a * x) = 4 * a := by ring
      rw [same]
      exact congrArg (fun r : ℝ => r / a ^ order) (mul_comm _ _)

variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def momentCLM (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ)
    (wave : Index → IntegerWavevector) : lp (fun _ : Index => E) 2 →L[ℝ] lp (fun _ : Index => E) 2 :=
  lp.mapCLM 2 (fun index => (frequencySize (wave index) ^ order *
    finiteStateVorticityHeatMultiplier nu.coeff lag (wave index)) • ContinuousLinearMap.id ℝ E)
    (budget_nonneg nu lag order) fun index => by
      apply ContinuousLinearMap.opNorm_le_bound _ (budget_nonneg nu lag order)
      intro value
      change ‖(frequencySize (wave index) ^ order *
        finiteStateVorticityHeatMultiplier nu.coeff lag (wave index)) • value‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (pow_nonneg (frequencySize_nonneg _) _) (finiteStateVorticityHeatMultiplier_nonneg _ _ _))]
      exact mul_le_mul_of_nonneg_right (multiplier_bound nu lag positive order (wave index)) (norm_nonneg _)

theorem momentCLM_row (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ)
    (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2) (index : Index) :
    momentCLM nu lag positive order wave value index =
      (frequencySize (wave index) ^ order * finiteStateVorticityHeatMultiplier nu.coeff lag (wave index)) • value index := rfl

theorem momentCLM_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ)
    (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2) :
    ‖momentCLM nu lag positive order wave value‖ ≤ budget nu lag order * ‖value‖ := by
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  exact mul_le_mul_of_nonneg_right
    (lp.norm_mapCLM_le _ _ (budget_nonneg nu lag order) _) (norm_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeHeatSpatialMultiplier
