import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredTensor
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.TensorClock

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredResponseClock
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeResponseTensorPayment NativeCenteredResponseTensor
open NativeWindowTraceDualEvolution (inverse lifted energy)
open NativeResponseTensorClock (clockInput)
noncomputable section
variable {nu : Viscosity}

def clockWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (w : physicalSpace (modes M)) : ℝ :=
  2*inner ℝ (tensor seed M F radius frame time w)
    (-tensor seed M F radius frame time (clockInput seed M F radius time w))

theorem tensor_rate_clock_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ)
    (w g : physicalSpace (modes M)) :
    pairTensor M (centered seed M frame time) (liftedRate seed M F radius time w g) =
      pairTensor M (centered seed M frame time)
        (inverse seed M F radius time (-NativeWindowTraceAdjoint.dual seed M time w-g))-
      tensor seed M F radius frame time (clockInput seed M F radius time w) := by
  rw [NativeResponseTensorClock.liftedRate_split]
  change pairTensorCLM M (centered seed M frame time) (_-_) =
    pairTensorCLM M (centered seed M frame time) _-pairTensorCLM M (centered seed M frame time) _
  exact map_sub _ _ _

theorem source_clock_work_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ radius ≥ low,∀ outerRadius M,
      ∀ frame∈Icc 0 horizon,∀ᵐ time : ℝ,time∈Icc 0 horizon →∀ w : physicalSpace (modes M),
      |clockWork seed M (integerWaveFrequencyCube outerRadius) radius frame time w| ≤
        C*(1+NativeUnheatedSourceGradient.mass seed time)*
          energy seed M (integerWaveFrequencyCube outerRadius) radius time w := by
  obtain ⟨first,K,K0,mixed⟩ := source_tensor_paid seed horizon nonnegative
  obtain ⟨last,B,B0,clock⟩ := NativeResponseClockPayment.source_inverse_clock_bound seed horizon nonnegative
  refine ⟨max first last,K*(1+B^2),by positivity,fun radius above outerRadius M frame framed => ?_⟩
  filter_upwards [mixed radius ((le_max_left first last).trans above) outerRadius M frame framed]
    with time source inside w
  let F := integerWaveFrequencyCube outerRadius
  let rate := clockInput seed M F radius time w
  let x := tensor seed M F radius frame time w
  let y := tensor seed M F radius frame time rate
  have base := source inside w
  have changed := source inside rate
  have energyBound := clock radius ((le_max_right first last).trans above) outerRadius M time inside w
  change energy seed M F radius time rate ≤ B^2*energy seed M F radius time w at energyBound
  have scaled := mul_le_mul_of_nonneg_left energyBound
    (show 0 ≤ K*(1+NativeUnheatedSourceGradient.mass seed time) from
      mul_nonneg K0 (add_nonneg zero_le_one (NativeUnheatedSourceGradient.mass_nonnegative seed time)))
  have pair : |2*inner ℝ x (-y)| ≤ ‖x‖^2+‖y‖^2 := by
    rw [inner_neg_right,mul_neg,abs_neg,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have bound := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y) (by norm_num : (0 : ℝ)≤2)
    nlinarith only [bound,sq_nonneg (‖x‖-‖y‖)]
  change ‖x‖^2 ≤ K*(1+NativeUnheatedSourceGradient.mass seed time)*energy seed M F radius time w at base
  change ‖y‖^2 ≤ K*(1+NativeUnheatedSourceGradient.mass seed time)*energy seed M F radius time rate at changed
  change |2*inner ℝ x (-y)| ≤ _
  nlinarith only [base,changed,scaled,pair]

end
end SaturationMonoid.NavierStokes.NativeCenteredResponseClock
