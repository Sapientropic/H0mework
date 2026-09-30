import H0mework.Versions.X.NavierStokes.PhysicalReadout.Fourier
import H0mework.NavierStokes.PhysicalReadout.EndpointVelocity

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeCofinalFluxPairing

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeEndpointVelocityCarrier NativePhysicalFourier NativeStressSource

noncomputable section

/-- A test vector for the entire convolution row, on the original velocity Hilbert carrier. -/
def fluxTest (right : WholeRestartVelocityEndpointState) (wave : IntegerWavevector)
    (output input : Coordinate) : WholeRestartVelocityEndpointState :=
  ⟨fun first => EuclideanSpace.single input (star (wholeVelocity right (wave - first.1) output)), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, PiLp.norm_single, norm_star]
    have full : Summable (fun frequency => ‖wholeVelocity right frequency output‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scalarSequence] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
          (scalarSequence (wholeVelocity right) output)).summable
    exact full.comp_injective (fun left right equality =>
      Subtype.ext (sub_right_injective equality))⟩

def bilinearFlux (left right : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  -∑' first : IntegerWavevector,
    wholeVelocity left first input * wholeVelocity right (wave - first) output

theorem bilinearFlux_diagonal (velocity : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    bilinearFlux velocity velocity wave output input = quadraticFlux (wholeVelocity velocity) wave output input := rfl

/-- A whole convolution with a fixed second factor is an actual continuous linear test. -/
theorem bilinearFlux_eq_inner (left right : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    bilinearFlux left right wave output input = -inner ℂ (fluxTest right wave output input) left := by
  rw [bilinearFlux, lp.inner_eq_tsum]
  congr 1
  have inclusion : Function.Injective (Subtype.val : NonzeroIntegerWavevector → IntegerWavevector) :=
    Subtype.val_injective
  rw [← inclusion.tsum_eq (fun first nonzero => by
    refine ⟨⟨first, ?_⟩, rfl⟩
    intro zero
    exact nonzero (by simp [zero]))]
  apply tsum_congr
  intro first
  change wholeVelocity left first.1 input * wholeVelocity right (wave - first.1) output =
    inner ℂ (EuclideanSpace.single input (star (wholeVelocity right (wave - first.1) output))) (left first)
  rw [EuclideanSpace.inner_single_left, starRingEnd_apply, star_star, wholeVelocity_nonzero]
  exact mul_comm _ _

theorem bilinearFlux_flip (left right : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    bilinearFlux left right wave output input = bilinearFlux right left wave input output := by
  unfold bilinearFlux
  congr 1
  calc
    _ = ∑' first, wholeVelocity left (wave - first) input * wholeVelocity right first output := by
      simpa only [outputSubEquiv, Equiv.coe_fn_mk, sub_sub_cancel] using
        (outputSubEquiv wave).tsum_eq (fun first =>
          wholeVelocity left first input * wholeVelocity right (wave - first) output) |>.symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

theorem bilinearFlux_sub_left (left other right : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    bilinearFlux (left - other) right wave output input =
      bilinearFlux left right wave output input - bilinearFlux other right wave output input := by
  simp only [bilinearFlux_eq_inner, inner_sub_right]
  ring

theorem bilinearFlux_sub_right (left right other : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    bilinearFlux left (right - other) wave output input =
      bilinearFlux left right wave output input - bilinearFlux left other wave output input := by
  rw [bilinearFlux_flip, bilinearFlux_sub_left,
    bilinearFlux_flip right left, bilinearFlux_flip other left]

theorem weak_bilinearFlux_left (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint right : WholeRestartVelocityEndpointState)
    (weak : ∀ test, Tendsto (fun index => inner ℂ (sequence index) test) atTop (nhds (inner ℂ endpoint test)))
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => bilinearFlux (sequence index) right wave output input) atTop
      (nhds (bilinearFlux endpoint right wave output input)) := by
  have paired := (continuous_star.tendsto _).comp (weak (fluxTest right wave output input))
  have conjugate (left right : WholeRestartVelocityEndpointState) :
      star (inner ℂ left right) = inner ℂ right left := inner_conj_symm _ _
  simpa only [Function.comp_def, conjugate, bilinearFlux_eq_inner] using paired.neg

theorem weak_bilinearFlux_right (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint left : WholeRestartVelocityEndpointState)
    (weak : ∀ test, Tendsto (fun index => inner ℂ (sequence index) test) atTop (nhds (inner ℂ endpoint test)))
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun index => bilinearFlux left (sequence index) wave output input) atTop
      (nhds (bilinearFlux left endpoint wave output input)) := by
  simpa only [bilinearFlux_flip left] using weak_bilinearFlux_left sequence endpoint left weak wave input output

theorem fluxTest_zero_diagonal_sum (velocity : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality velocity) :
    (∑ coordinate : Coordinate, fluxTest velocity 0 coordinate coordinate) = velocity := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  have reflected (direction : Coordinate) :
      wholeVelocity velocity (0 - wave.1) direction = star (velocity wave direction) := by
    have waveEq : 0 - wave.1 = (nonzeroIntegerWavevectorNeg wave).1 := by
      funext index
      simp [nonzeroIntegerWavevectorNeg, waveNeg]
    rw [waveEq, wholeVelocity_nonzero, reality wave direction]
  change (∑ direction : Coordinate, fluxTest velocity 0 direction direction wave) coordinate = _
  simp only [fluxTest, reflected, star_star]
  simp

/-- The zero-wave trace is the full original velocity norm, including every frequency. -/
theorem bilinearFlux_zero_trace (velocity : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality velocity) :
    (∑ coordinate : Coordinate, (bilinearFlux velocity velocity 0 coordinate coordinate).re) =
      -‖velocity‖ ^ 2 := by
  simp only [bilinearFlux_eq_inner, Complex.neg_re, Finset.sum_neg_distrib]
  rw [← Complex.re_sum, ← sum_inner, fluxTest_zero_diagonal_sum velocity reality]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) velocity

end
end SaturationMonoid.NavierStokes.NativeCofinalFluxPairing
