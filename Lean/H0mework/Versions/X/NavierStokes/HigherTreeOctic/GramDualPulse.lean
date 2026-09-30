import H0mework.Versions.X.NavierStokes.HigherTreeOctic.ThetaTrace
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDualPulse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeEndpointVelocityCarrier
open NativeUnheatedOcticThetaGram
noncomputable section
variable {nu : Viscosity}
abbrev Vector := EuclideanSpace ℂ Coordinate
abbrev Pulse := Lp Vector 2 (volume.restrict (Ioi (0 : ℝ)))
abbrev Space := lp (fun _ : IntegerWavevector => Pulse) 2

def profile (rest : ℝ) (wave : IntegerWavevector) (auxiliary : ℝ) : Vector :=
  WithLp.toLp 2 (fun direction => (feature nu (2*rest) wave direction auxiliary : ℂ))

theorem profile_square (rest : ℝ) (wave : IntegerWavevector) (auxiliary : ℝ) :
    ‖profile (nu := nu) rest wave auxiliary‖^2 = ∑ direction : Coordinate, feature nu (2*rest) wave direction auxiliary^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [profile, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem profile_paid (rest : ℝ) (nonnegative : 0 ≤ rest) (wave : IntegerWavevector) :
    MemLp (profile (nu := nu) rest wave) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have measured : AEStronglyMeasurable (profile (nu := nu) rest wave) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold profile feature
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm measured).mpr
  simp_rw [profile_square]
  simpa only [pow_two] using gram_integrable (nu := nu) (2*rest) (by linarith) wave wave

def pulse (rest : ℝ) (nonnegative : 0 ≤ rest) (wave : IntegerWavevector) : Pulse :=
  (profile_paid rest nonnegative wave).toLp (profile (nu := nu) rest wave)

theorem pulse_ae (rest : ℝ) (nonnegative : 0 ≤ rest) (wave : IntegerWavevector) :
    pulse (nu := nu) rest nonnegative wave =ᵐ[volume.restrict (Ioi 0)] profile (nu := nu) rest wave := MemLp.coeFn_toLp _

theorem profile_inner (firstRest lastRest : ℝ) (first last : IntegerWavevector) (auxiliary : ℝ) :
    inner ℂ (profile (nu := nu) firstRest first auxiliary) (profile (nu := nu) lastRest last auxiliary) =
      ((∑ direction : Coordinate, feature nu (firstRest+lastRest) first direction auxiliary*
        feature nu (firstRest+lastRest) last direction auxiliary : ℝ) : ℂ) := by
  have same (direction : Coordinate) :
      feature nu (2*firstRest) first direction auxiliary*feature nu (2*lastRest) last direction auxiliary =
      feature nu (firstRest+lastRest) first direction auxiliary*feature nu (firstRest+lastRest) last direction auxiliary := by
    unfold feature
    have exponents : -(2*firstRest/2+rate nu first)*auxiliary + -(2*lastRest/2+rate nu last)*auxiliary =
        -((firstRest+lastRest)/2+rate nu first)*auxiliary + -((firstRest+lastRest)/2+rate nu last)*auxiliary := by ring
    calc
      _ = (Real.sqrt (2*nu.coeff*(2*Real.pi)^2)*(first direction : ℝ))*(Real.sqrt (2*nu.coeff*(2*Real.pi)^2)*(last direction : ℝ))*
          Real.exp (-(2*firstRest/2+rate nu first)*auxiliary + -(2*lastRest/2+rate nu last)*auxiliary) := by rw [Real.exp_add]; ring
      _ = _ := by rw [exponents, Real.exp_add]; ring
  rw [PiLp.inner_apply]
  simp only [profile, PiLp.toLp_apply, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun direction _ => congrArg Complex.ofReal ((mul_comm _ _).trans (same direction))

theorem pulse_inner (firstRest lastRest : ℝ) (first0 : 0 ≤ firstRest) (last0 : 0 ≤ lastRest) (first last : IntegerWavevector) :
    inner ℂ (pulse (nu := nu) firstRest first0 first) (pulse (nu := nu) lastRest last0 last) =
      (kernel nu (firstRest+lastRest) first last : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ auxiliary in Ioi (0 : ℝ), ((∑ direction : Coordinate,
        feature nu (firstRest+lastRest) first direction auxiliary*feature nu (firstRest+lastRest) last direction auxiliary : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [pulse_ae firstRest first0 first, pulse_ae lastRest last0 last] with auxiliary firstRead lastRead
      rw [firstRead, lastRead, profile_inner]
    _ = _ := by rw [integral_complex_ofReal, laplace_gram _ (add_nonneg first0 last0)]

theorem pulse_norm (rest : ℝ) (nonnegative : 0 ≤ rest) (wave : IntegerWavevector) :
    ‖pulse (nu := nu) rest nonnegative wave‖ ≤ 1 := by
  have square : ‖pulse (nu := nu) rest nonnegative wave‖^2 = kernel nu (rest+rest) wave wave := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), pulse_inner]
    rfl
  have paid : kernel nu (rest+rest) wave wave ≤ 1 :=
    (le_abs_self _).trans (kernel_bound (rest+rest) (add_nonneg nonnegative nonnegative) wave wave)
  rw [← square] at paid
  nlinarith [norm_nonneg (pulse (nu := nu) rest nonnegative wave)]

def source (value : WholeRestartVelocityEndpointState) (coordinate : Coordinate) : Space :=
  ⟨fun wave => star (wholeVelocity value wave coordinate) • pulse (nu := nu) 0 le_rfl wave,
    (lp.memℓp (wholeVelocity value)).mono' (fun wave => by
      rw [norm_smul, norm_star]
      exact (mul_le_mul_of_nonneg_left (pulse_norm 0 le_rfl wave) (norm_nonneg _)).trans
        (by simpa only [mul_one] using norm_le_pi_norm (wholeVelocity value wave) coordinate))⟩

theorem source_bound (value : WholeRestartVelocityEndpointState) (coordinate : Coordinate) :
    ‖source (nu := nu) value coordinate‖ ≤ ‖value‖ := by
  apply le_trans (b := ‖wholeVelocity value‖) _ (wholeVelocity_norm_le value)
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖star (wholeVelocity value wave coordinate) • pulse (nu := nu) 0 le_rfl wave‖ ≤ _
  rw [norm_smul, norm_star]
  exact (mul_le_mul_of_nonneg_left (pulse_norm 0 le_rfl wave) (norm_nonneg _)).trans
    (by simpa only [mul_one] using norm_le_pi_norm (wholeVelocity value wave) coordinate)

theorem source_single (value : WholeRestartVelocityEndpointState) (coordinate : Coordinate) (inside wave : IntegerWavevector)
    (rest : ℝ) (nonnegative : 0 ≤ rest) (coefficient : ℂ) :
    inner ℂ (source (nu := nu) value coordinate) (lp.single 2 inside (coefficient • pulse (nu := nu) rest nonnegative wave)) =
      (kernel nu rest inside wave : ℂ)*wholeVelocity value inside coordinate*coefficient := by
  rw [lp.inner_single_right]
  change inner ℂ (star (wholeVelocity value inside coordinate) • pulse (nu := nu) 0 le_rfl inside)
    (coefficient • pulse (nu := nu) rest nonnegative wave) = _
  rw [inner_smul_left, inner_smul_right, pulse_inner]
  simp only [starRingEnd_apply, star_star, zero_add]
  ring

theorem single_inner (firstKey lastKey first last : IntegerWavevector) (firstRest lastRest : ℝ)
    (first0 : 0 ≤ firstRest) (last0 : 0 ≤ lastRest) (firstCoefficient lastCoefficient : ℂ) :
    inner ℂ (lp.single 2 firstKey (firstCoefficient • pulse (nu := nu) firstRest first0 first) : Space)
      (lp.single 2 lastKey (lastCoefficient • pulse (nu := nu) lastRest last0 last)) =
    if firstKey=lastKey then star firstCoefficient*lastCoefficient*(kernel nu (firstRest+lastRest) first last : ℂ) else 0 := by
  classical
  rw [lp.inner_single_left]
  by_cases same : firstKey=lastKey
  · subst lastKey
    simp only [lp.single_apply, Pi.single_eq_same, if_true, inner_smul_left, inner_smul_right, pulse_inner, starRingEnd_apply]
    ring
  · simp only [lp.single_apply, Pi.single_eq_of_ne same, inner_zero_right, if_neg same]

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDualPulse
