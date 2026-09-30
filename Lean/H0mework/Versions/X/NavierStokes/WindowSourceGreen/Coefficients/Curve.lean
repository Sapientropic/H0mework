import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerWeakSource
import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.Continuity
import Mathlib.Topology.UniformSpace.Dini

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeForwardWindowEvolution (velocityJet)
open NativeWindowSobolevVelocity (multiplier state state_row)
noncomputable section
variable {nu : Viscosity}

def observe (F : Finset NonzeroIntegerWavevector) : WholeRestartVelocityEndpointState →L[ℝ]
    PiLp 2 (fun _ : F => ComplexCoordinateEuclidean) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : F => (multiplier k.1.1) • lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 k.1)

theorem observe_apply (F : Finset NonzeroIntegerWavevector) (v : WholeRestartVelocityEndpointState) (k : F) :
    observe F v k=multiplier k.1.1 • v k.1 := rfl

def curve (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (time : Icc (0:ℝ) horizon) : WholeRestartVelocityEndpointState :=
  state seed order time (by linarith [time.property.1])

theorem observed_derivative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset NonzeroIntegerWavevector) (time : ℝ) :
    HasDerivAt (fun t => observe F (velocityJet seed order t))
      (observe F (velocityJet seed (order+1) time)) time := by
  exact (observe F).hasFDerivAt.comp_hasDerivAt time
    (NativeForwardWindowEvolution.velocityJet_hasDerivAt seed order time)

theorem observed_square (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset NonzeroIntegerWavevector) (time : ℝ) (valid : -1<time) :
    ‖observe F (velocityJet seed order time)‖^2=∑ k∈F,‖state seed order time valid k‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ k : F, ‖multiplier k.1.1 • velocityJet seed order time k.1‖^2)=_
  simp only [state_row]
  exact Finset.sum_coe_sort F (fun k => ‖multiplier k.1 • velocityJet seed order time k‖^2)

theorem observed_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (F : Finset NonzeroIntegerWavevector) (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖observe F (velocityJet seed order time)‖≤Real.sqrt (NativeWindowSobolevVelocity.budget seed order horizon) := by
  apply Real.le_sqrt_of_sq_le
  have valid : -1<time:=by linarith [inside.1]
  rw [observed_square seed order F time valid]
  simp only [state_row,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevVelocity.multiplier_sq]
  exact ((NativeWindowSobolevVelocity.weighted_summable seed order time valid).sum_le_tsum F
    (fun wave _ => by positivity [integerWaveNormSq_nonneg wave.1])).trans
      (NativeWindowSobolevVelocity.moment_bound_on_interval seed order time horizon valid inside.2)


theorem observed_difference_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset NonzeroIntegerWavevector) (horizon first last : ℝ)
    (first_in : first ∈ Icc 0 horizon) (last_in : last ∈ Icc 0 horizon) :
    ‖observe F (velocityJet seed order last)-observe F (velocityJet seed order first)‖ ≤
      Real.sqrt (NativeWindowSobolevVelocity.budget seed (order+1) horizon)*‖last-first‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun time _ => (observed_derivative seed order F time).hasDerivWithinAt)
    (fun time inside => observed_bound seed (order+1) horizon F time inside)
    (convex_Icc 0 horizon) first_in last_in

theorem observed_difference_square (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (F : Finset NonzeroIntegerWavevector) (horizon : ℝ) (first last : Icc (0 : ℝ) horizon) :
    (∑ wave ∈ F, ‖(curve seed order horizon last-curve seed order horizon first) wave‖^2) =
      ‖observe F (velocityJet seed order last)-observe F (velocityJet seed order first)‖^2 := by
  rw [← map_sub,PiLp.norm_sq_eq_of_L2]
  change _=∑ k : F, ‖multiplier k.1.1 • (velocityJet seed order last k.1-velocityJet seed order first k.1)‖^2
  calc
    _=∑ wave∈F, ‖multiplier wave.1 • (velocityJet seed order last wave-velocityJet seed order first wave)‖^2 := by
      apply Finset.sum_congr rfl
      intro wave _
      change ‖multiplier wave.1 • velocityJet seed order last wave-
        multiplier wave.1 • velocityJet seed order first wave‖^2=_
      rw [smul_sub]
    _=_ := (Finset.sum_coe_sort F (fun wave =>
      ‖multiplier wave.1 • (velocityJet seed order last wave-velocityJet seed order first wave)‖^2)).symm

theorem curve_lipschitz (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    LipschitzWith ‖Real.sqrt (NativeWindowSobolevVelocity.budget seed (order+1) horizon)‖₊
      (curve seed order horizon) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  simp only [Subtype.dist_eq,dist_eq_norm]
  change ‖curve seed order horizon first-curve seed order horizon last‖ ≤
    ‖Real.sqrt (NativeWindowSobolevVelocity.budget seed (order+1) horizon)‖*‖(first : ℝ)-(last : ℝ)‖
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
    (mul_le_mul_of_nonneg_right (le_abs_self (Real.sqrt (NativeWindowSobolevVelocity.budget seed (order+1) horizon))) (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) paid 2

theorem curve_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    Continuous (curve seed order horizon) := (curve_lipschitz seed order horizon).continuous



end
end SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientForm
