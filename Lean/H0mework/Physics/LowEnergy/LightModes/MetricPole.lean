import H0mework.Physics.LowEnergy.LightModes.MetricCoefficients
import H0mework.Physics.LowEnergy.LightModes.Derivative
import H0mework.Physics.LowEnergy.LightModes.Pole
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The original g00 numerator remains nonzero on the actual generated
axial branch. Its genuine residue follows without a caller visibility premise. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Filter Topology
noncomputable section

theorem metric_root_numerator_negative (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    metricRaw (q^2*(sourceRoot .axialPhase).root (q^2)) (q^2)<0 := by
  let r := (sourceRoot .axialPhase).root (q^2)
  have inside := (sourceRoot .axialPhase).root_in_window (q^2)
  have rbound : |r|≤2 := (sourceRoot .axialPhase).window_bound r inside
  have qbound : |q|≤1 := small.trans momentumRadius_bound
  have error : |q*value metricTerms r q|≤metricMargin/2 := by
    rw [abs_mul]
    apply le_trans (mul_le_mul small (value_bound metricTerms r q rbound qbound)
      (abs_nonneg _) momentumRadius_positive.le)
    exact metric_remainder_small
  have lower : (125/162 : ℝ)-1/20≤r := inside.1
  have principal := metric_linear_negative r lower
  have negative : metricLinear r+q*value metricTerms r q<0 := by
    linarith [le_abs_self (q*value metricTerms r q),metric_margin_positive]
  rw [metric_normalized]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero nonzero) negative

def metricNumerator (z : ℂ) (q : ℝ) : ℂ :=
  ((Real.sqrt 30 : ℂ)/3125)*metricRaw (z^2) ((q : ℂ)^2)

theorem metric_raw_cast (v w : ℝ) : metricRaw (v : ℂ) (w : ℂ)=(metricRaw v w : ℝ) := by
  simp [metricRaw]

theorem original_metric_numerator_nonzero (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    metricNumerator (sourceWave .axialPhase q) q≠0 := by
  have negative := metric_root_numerator_negative q small nonzero
  have square := source_wave_square .axialPhase q
  have power : sourcePower .axialPhase=1 := rfl
  rw [power,pow_one] at square
  generalize hr : (sourceRoot .axialPhase).root (q^2)=r at square negative
  unfold metricNumerator
  apply mul_ne_zero
  · apply div_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    · norm_num
  · rw [square,← Complex.ofReal_pow,metric_raw_cast]
    exact Complex.ofReal_ne_zero.mpr negative.ne

def axialTimeDerivative (q : ℝ) : ℂ :=
  (complexSquaredPolynomial .axialPhase (q^2)).derivative.eval ((sourceWave .axialPhase q)^2)*
    (2*sourceWave .axialPhase q)

theorem original_metric_true_pole (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    Tendsto (fun z : ℂ => (z-sourceWave .axialPhase q)*
      (metricNumerator z q/sourceFactor .axialPhase (z^2) ((q : ℂ)^2)))
      (𝓝[≠] (sourceWave .axialPhase q))
      (𝓝 (metricNumerator (sourceWave .axialPhase q) q/axialTimeDerivative q)) ∧
    metricNumerator (sourceWave .axialPhase q) q/axialTimeDerivative q≠0 := by
  have derivative := source_complex_simple .axialPhase q small nonzero
  have root := source_wave_on_shell .axialPhase q small
  have regular : ContinuousAt (fun z : ℂ => metricNumerator z q) (sourceWave .axialPhase q) := by
    unfold metricNumerator metricRaw
    fun_prop
  have generated := source_pole_nonzero (fun z : ℂ => sourceFactor .axialPhase (z^2) ((q : ℂ)^2))
    (fun z => metricNumerator z q) (sourceWave .axialPhase q) _ derivative.1 root derivative.2 regular
      (original_metric_numerator_nonzero q small nonzero)
  exact ⟨generated.1,generated.2.1⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
