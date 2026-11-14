import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactEuler
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open FourierTransform
open scoped Topology ContDiff FourierTransform BoundedContinuousFunction

open private compact_join_supported counted_phase_input_support from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactEuler


local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "S'" => TemperedDistribution ℝ ℂ

private def wavePhase (ξ x : ℝ) : ℂ := Complex.exp (-2 * (Real.pi : ℂ)*Complex.I*(ξ : ℂ)*(x : ℂ))

private theorem fourier_phase_integral (v : ℝ → ℂ) (ξ : ℝ) :
    𝓕 v ξ = ∫ x, wavePhase ξ x*v x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, wavePhase]
  apply congrArg (fun t : ℂ => Complex.exp t * v x)
  push_cast
  ring

private theorem wave_first_moment (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0) :
    Integrable (fun x : ℝ => x • compactPhaseJoin z x) := by
  let u := compactPhaseJoin z
  have integrable := L1.integrable_coeFn u
  apply (integrable.norm.mul_const q).mono'
    (continuous_id.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  filter_upwards [compact_join_supported z support] with x outside
  change ‖x • u x‖ ≤ ‖u x‖*q
  by_cases inside : |x| ≤ q
  · rw [norm_smul, Real.norm_eq_abs, mul_comm ‖u x‖]
    exact mul_le_mul_of_nonneg_right inside (norm_nonneg _)
  · rw [show u x = 0 from outside (lt_of_not_ge inside), smul_zero, norm_zero, zero_mul]

private theorem compact_wave_hasDerivAt (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0) (ξ : ℝ) :
    HasDerivAt (fun t => compactPhaseWave z t)
      (𝓕 (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • compactPhaseJoin z x) ξ) ξ :=
  Real.hasDerivAt_fourier (L1.integrable_coeFn (compactPhaseJoin z)) (wave_first_moment z support) ξ

/-- On the compact fibre the exact Euler effect generates the ordinary
pointwise frequency equation. -/
theorem compact_wave_euler (c : BurnolCompletedMellinCoordinate)
    (output input : L¹ × BurnolL2) (scale : ℂ)
    (outputSupport : ∀ᵐ x : ℝ ∂volume, q < |x| → output.1 x = 0 ∧ output.2 x = 0)
    (inputSupport : ∀ᵐ x : ℝ ∂volume, q < |x| → input.1 x = 0 ∧ input.2 x = 0)
    (equation : eulerOfPhysicalSplit c output = scale • distributionOfSplit input)
    (ξ : ℝ) :
    (ξ : ℂ)*deriv (fun t => compactPhaseWave output t) ξ+
      (1-star c.value)*compactPhaseWave output ξ = -scale*compactPhaseWave input ξ := by
  let k := -2 * (Real.pi : ℂ)*Complex.I*(ξ : ℂ)
  let φ := wavePhase ξ
  have linear : ContDiff ℝ ∞ (fun x : ℝ => k*(x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have smooth : ContDiff ℝ ∞ φ := linear.cexp
  have rate (x : ℝ) : deriv φ x = k*φ x := by
    have exactRate := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul k).cexp
    change deriv (fun y : ℝ => Complex.exp (k*(y : ℂ))) x = k*Complex.exp (k*(x : ℂ))
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm (Complex.exp _)]
      using exactRate.deriv
  have outputWave : compactPhaseWave output ξ = ∫ x, φ x*compactPhaseJoin output x :=
    fourier_phase_integral _ _
  have inputWave : compactPhaseWave input ξ = ∫ x, φ x*compactPhaseJoin input x :=
    fourier_phase_integral _ _
  have derivative : (ξ : ℂ)*deriv (fun t => compactPhaseWave output t) ξ =
      ∫ x : ℝ, (x : ℂ)*deriv φ x*compactPhaseJoin output x := by
    rw [(compact_wave_hasDerivAt output outputSupport ξ).deriv, fourier_phase_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [rate x, smul_eq_mul]
    change (ξ : ℂ)*(φ x*((-2 * (Real.pi : ℂ)*Complex.I*(x : ℂ))*compactPhaseJoin output x)) =
      (x : ℂ)*(k*φ x)*compactPhaseJoin output x
    dsimp only [k]
    ring
  have source := compact_euler_smooth_read c output input scale outputSupport inputSupport equation φ smooth
  rw [← outputWave, ← derivative, ← inputWave] at source
  linear_combination -source

private def positionMoment (j : Nat) (z : L¹ × BurnolL2) : ℂ :=
  ∫ x : ℝ, (x : ℂ)^j*compactPhaseJoin z x

/-- All polynomial moments are generated by the same finite R source. -/
theorem actual_counted_compact_phase_moments (c : BurnolCompletedMellinCoordinate) (n j : Nat) :
    (1+(j : ℂ)-star c.value)*positionMoment j (countedCompactPhaseField c n) =
      2*positionMoment j (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)) := by
  let u := countedCompactPhaseField c n
  let v := splitAtPhysicalCutoff r₀ (countedPhaseSource c n)
  let φ := fun x : ℝ => (x : ℂ)^j
  have smooth : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.pow j
  have rate (x : ℝ) : (x : ℂ)*deriv φ x = (j : ℂ)*φ x := by
    cases j with
    | zero => simp [φ]
    | succ k =>
      have derivative := ((Complex.ofRealCLM.hasDerivAt (x := x)).pow (k+1)).deriv
      simp only [Complex.ofRealCLM_apply, Nat.add_sub_cancel, Complex.ofReal_one, mul_one] at derivative
      change deriv (fun t : ℝ => (t : ℂ)^(k+1)) x = ((k+1 : Nat) : ℂ)*(x : ℂ)^k at derivative
      change (x : ℂ)*deriv (fun t : ℝ => (t : ℂ)^(k+1)) x =
        ((k+1 : Nat) : ℂ)*(x : ℂ)^(k+1)
      rw [derivative, pow_succ]
      ring
  have source := compact_euler_smooth_read c u v (-(2 : ℂ)) (actual_counted_compact_phase_support c n)
    (counted_phase_input_support c n) (actual_counted_compact_phase_euler c n) φ smooth
  have moment : (∫ x : ℝ, (x : ℂ)*deriv φ x*compactPhaseJoin u x) = (j : ℂ)*positionMoment j u := by
    rw [positionMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [rate x, mul_assoc]
  rw [moment] at source
  change (star c.value-1)*positionMoment j u-(j : ℂ)*positionMoment j u =
    -(2 : ℂ)*positionMoment j v at source
  linear_combination -source

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
