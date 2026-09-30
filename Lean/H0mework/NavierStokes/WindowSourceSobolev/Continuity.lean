import H0mework.NavierStokes.UnheatedWriterSobolev.Stress
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevContinuity
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeForwardWindowJets
open NativeWindowSobolevStress
noncomputable section
variable {nu : Viscosity}

theorem observed_derivative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset IntegerWavevector) (time : ℝ) :
    HasDerivAt (fun parameter => observe F (NativeUnheatedWindowStress.stress seed order parameter))
      (observe F (NativeUnheatedWindowStress.stress seed (order+1) time)) time := by
  let action := (observeCLM F).comp
    (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  exact action.hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed order time)

theorem observed_difference_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset IntegerWavevector) (horizon first last : ℝ)
    (first_in : first ∈ Icc 0 horizon) (last_in : last ∈ Icc 0 horizon) :
    ‖observe F (NativeUnheatedWindowStress.stress seed order last)-
      observe F (NativeUnheatedWindowStress.stress seed order first)‖ ≤
      budget seed (order+1) horizon*‖last-first‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun time _ => (observed_derivative seed order F time).hasDerivWithinAt)
    (fun time inside => observed_bound_on_interval seed (order+1) time horizon (by linarith [inside.1]) inside.2 F)
    (convex_Icc 0 horizon) first_in last_in

def curve (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (time : Icc (0 : ℝ) horizon) : Space := state seed order time (by linarith [time.property.1])

theorem observed_difference_square (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset IntegerWavevector) (horizon : ℝ) (first last : Icc (0 : ℝ) horizon) :
    (∑ wave ∈ F, ‖(curve seed order horizon last-curve seed order horizon first) wave‖^2) =
      ‖observe F (NativeUnheatedWindowStress.stress seed order last)-
        observe F (NativeUnheatedWindowStress.stress seed order first)‖^2 := by
  have same : observe F (NativeUnheatedWindowStress.stress seed order last)-
      observe F (NativeUnheatedWindowStress.stress seed order first) =
      observe F (NativeUnheatedWindowStress.stress seed order last-NativeUnheatedWindowStress.stress seed order first) := by
    ext entry
    simp only [observe,PiLp.sub_apply,Pi.sub_apply,smul_sub]
  rw [same,observe_norm_sq]
  apply Finset.sum_congr rfl
  intro wave _
  change ‖quarter wave • tensor (NativeUnheatedWindowStress.stress seed order last wave)-
    quarter wave • tensor (NativeUnheatedWindowStress.stress seed order first wave)‖^2 = _
  rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,quarter_sq]
  rfl

theorem curve_lipschitz (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    LipschitzWith ‖budget seed (order+1) horizon‖₊ (curve seed order horizon) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  simp only [Subtype.dist_eq,dist_eq_norm]
  change ‖curve seed order horizon first-curve seed order horizon last‖ ≤
    ‖budget seed (order+1) horizon‖*‖(first : ℝ)-(last : ℝ)‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have total := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (curve seed order horizon first-curve seed order horizon last)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at total
  rw [total]
  have summable := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (curve seed order horizon first-curve seed order horizon last)).summable
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at summable
  apply summable.tsum_le_of_sum_le
  intro F
  rw [observed_difference_square]
  have paid := (observed_difference_bound seed order F horizon last first last.property first.property).trans
    (mul_le_mul_of_nonneg_right (le_abs_self (budget seed (order+1) horizon)) (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) paid 2

theorem curve_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    Continuous (curve seed order horizon) := (curve_lipschitz seed order horizon).continuous

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevContinuity
