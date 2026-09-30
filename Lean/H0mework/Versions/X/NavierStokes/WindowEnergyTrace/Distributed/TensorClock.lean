import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.TensorTime
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Clock

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponseTensorClock
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeResponseTensorPayment
open NativeWindowTraceDualEvolution (mass inverse lifted energy)
noncomputable section
variable {nu : Viscosity}

def clockInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (w : physicalSpace (modes M)) :=
  deriv (mass seed M F radius) time (lifted seed M F radius time w)

def clockWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (w : physicalSpace (modes M)) : ℝ :=
  2*inner ℝ (mixedTensor seed M F radius time w)
    (-mixedTensor seed M F radius time (clockInput seed M F radius time w))

theorem liftedRate_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (w g : physicalSpace (modes M)) :
    liftedRate seed M F radius time w g =
      inverse seed M F radius time (-NativeWindowTraceAdjoint.dual seed M time w-g)-
        lifted seed M F radius time (clockInput seed M F radius time w) := by
  simp only [liftedRate,clockInput,lifted,map_sub]

theorem tensor_rate_clock_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (w g : physicalSpace (modes M)) :
    pairTensor M (NativeWindowTraceAdjoint.value seed M time) (liftedRate seed M F radius time w g) =
      pairTensor M (NativeWindowTraceAdjoint.value seed M time)
        (inverse seed M F radius time (-NativeWindowTraceAdjoint.dual seed M time w-g))-
      mixedTensor seed M F radius time (clockInput seed M F radius time w) := by
  rw [liftedRate_split]
  change pairTensorCLM M (NativeWindowTraceAdjoint.value seed M time) (_-_) =
    pairTensorCLM M (NativeWindowTraceAdjoint.value seed M time) _-
    pairTensorCLM M (NativeWindowTraceAdjoint.value seed M time) _
  exact map_sub _ _ _

theorem source_tensor_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M observation
      (test : physicalSpace (modes M)) a b (ab : a ≤ b),
      ∀ᵐ time : ℝ, time ∈ Ioo a b → time ∈ Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ab
      let u := NativeWindowTraceAdjoint.value seed M time
      let z := lifted seed M F radius time (p time)
      HasDerivAt (fun t => mixedTensor seed M F radius t (p t))
        (pairTensor M (NativeWindowTraceAdjoint.forward seed M time u+
            NativeWindowStageNineSource.forcing seed M time) z+
          pairTensor M u (inverse seed M F radius time
            (-NativeWindowTraceAdjoint.dual seed M time (p time)-
              load (nu := nu) observation M test time))-
          mixedTensor seed M F radius time (clockInput seed M F radius time (p time))) time := by
  obtain ⟨low,source⟩ := NativeResponseTensorPayment.source_tensor_rate seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M observation test a b ab => ?_⟩
  filter_upwards [source radius above outerRadius M observation test a b ab] with time actual physical clock
  have paid := actual physical clock
  dsimp only at paid ⊢
  rw [tensor_rate_clock_split] at paid
  simpa only [add_sub_assoc] using paid

private theorem squared_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    |2*inner ℝ x (-y)| ≤ ‖x‖^2+‖y‖^2 := by
  rw [inner_neg_right,mul_neg,abs_neg,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have paired := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y) (by norm_num : (0 : ℝ)≤2)
  nlinarith only [paired,sq_nonneg (‖x‖-‖y‖)]

theorem source_clock_work_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ᵐ time : ℝ, time ∈ Icc 0 horizon → ∀ w : physicalSpace (modes M),
      |clockWork seed M (integerWaveFrequencyCube outerRadius) radius time w| ≤
        C*NativeUnheatedSourceGradient.mass seed time*
          energy seed M (integerWaveFrequencyCube outerRadius) radius time w := by
  obtain ⟨first,mixed⟩ := source_mixed_tensor_paid seed horizon nonnegative
  obtain ⟨last,B,B0,clock⟩ := NativeResponseClockPayment.source_inverse_clock_bound seed horizon nonnegative
  let K := 288*NativeUnheatedRieszKernel.constant/(nu.coeff*(2*Real.pi)^2)
  have K0 : 0 ≤ K := by
    dsimp only [K]
    positivity [NativeUnheatedRieszKernel.constant_nonnegative,nu.coeff_pos]
  refine ⟨max first last,K*(1+B^2),by positivity,fun radius above outerRadius M => ?_⟩
  filter_upwards [mixed radius ((le_max_left first last).trans above) outerRadius M] with time source inside w
  let F := integerWaveFrequencyCube outerRadius
  let rate := clockInput seed M F radius time w
  have base := source inside w
  have changed := source inside rate
  have energyBound := clock radius ((le_max_right first last).trans above) outerRadius M time inside w
  change energy seed M F radius time rate ≤ B^2*energy seed M F radius time w at energyBound
  have scaled := mul_le_mul_of_nonneg_left energyBound
    (mul_nonneg K0 (NativeUnheatedSourceGradient.mass_nonnegative seed time))
  have pair := squared_pair (mixedTensor seed M F radius time w) (mixedTensor seed M F radius time rate)
  change ‖mixedTensor seed M F radius time w‖^2 ≤ K*NativeUnheatedSourceGradient.mass seed time*
    energy seed M F radius time w at base
  change ‖mixedTensor seed M F radius time rate‖^2 ≤ K*NativeUnheatedSourceGradient.mass seed time*
    energy seed M F radius time rate at changed
  change |2*inner ℝ (mixedTensor seed M F radius time w) (-mixedTensor seed M F radius time rate)| ≤ _
  nlinarith only [base,changed,scaled,pair]

end
end SaturationMonoid.NavierStokes.NativeResponseTensorClock
