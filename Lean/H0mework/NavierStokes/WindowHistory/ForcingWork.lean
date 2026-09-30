import H0mework.NavierStokes.WindowHistoryOseen.Equation
import H0mework.NavierStokes.WindowHistoryOseen.Gap
import H0mework.NavierStokes.WindowEnergyTraceCut.CutActionPhysical

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryForcingWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativePhysicalPairing NativeWholeResolvent
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowTraceWholeHistory (H finiteHistory gradient)
open NativeWindowHistoryOseen (forcingHistory action)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def massForm (M : ℕ) : NativeResolventCompactness.State →L[ℝ] NativeResolventCompactness.State →L[ℝ] ℝ :=
  let read := (LinearMap.toContinuousLinearMap (coefficients (modes M))).comp (NativeWindowStageNineSource.lift (modes M))
  (innerSL ℝ).bilinearComp read read

def massJet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → ℝ :=
  NativeWindowHierarchyPairWindow.window seed (massForm M) order

theorem mass_sample (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHierarchyPairWindow.pair seed (massForm M) time=
      ‖coefficients (modes M) (NativeWindowTraceAdjoint.value seed M time)‖^2 :=
  real_inner_self_eq_norm_sq (coefficients (modes M) (NativeWindowTraceAdjoint.value seed M time))

theorem mass_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖finiteHistory seed time M‖^2=massJet seed M 0 time := by
  have average : (∫ shift,NativeWindowHierarchyPairWindow.pair seed (massForm M) (time-shift) ∂averageMeasure)=massJet seed M 0 time := by
    rw [NativeForwardWindowPairingReadout.density_integral]
    rfl
  apply (NativeWindowTraceWholeHistory.norm_square (finiteHistory seed time M)).trans
  apply Eq.trans _ average
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryOseen.history_original seed M time] with shift original
  rw [original,NativeWindowHistoryOseen.velocityPath,include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (mass_sample seed M (time-shift)).symm

theorem mass_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (massJet seed M order) (massJet seed M (order+1) time) time :=
  NativeWindowHierarchyPairWindow.window_hasDerivAt seed (massForm M) order time

theorem mass_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    ‖massJet seed M order time‖ ≤ NativeWindowFiniteStressUniform.kernelBound order*(NativeUnifiedCompleteSource.budget seed)^2 := by
  rw [massJet,NativeWindowHierarchyPairWindow.window_original]
  have point (sample : ℝ) (inside : sample∈Set.uIoc (time+1) (time+2)) :
      ‖NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample •
        NativeWindowHierarchyPairWindow.pair seed (massForm M) sample‖ ≤
        NativeWindowFiniteStressUniform.kernelBound order*(NativeUnifiedCompleteSource.budget seed)^2 := by
    rw [uIoc_of_le (by linarith : time+1 ≤ time+2)] at inside
    rw [norm_smul,mass_sample,Real.norm_of_nonneg (sq_nonneg _)]
    simp only [NativeUnheatedStressPairEvolution.kernelWeight,zero_add]
    exact mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample))
      (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowTraceAdjoint.value_mass_bound seed M sample (by linarith [inside.1])) 2)
      (sq_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have paid := intervalIntegral.norm_integral_le_of_norm_le_const point
  simpa only [show time+2-(time+1)=(1 : ℝ) by ring,abs_one,mul_one] using paid

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (forcingHistory seed M time)

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    work seed M time=(1/2 : ℝ)*massJet seed M 1 time+nu.coeff*gradient M (finiteHistory seed time M) := by
  have derived : HasDerivAt (massJet seed M 0)
      (2*inner ℝ (finiteHistory seed time M) (NativeWindowHistoryOseen.rateHistory seed M time)) time := by
    simpa only [mass_original] using! HasDerivAt.norm_sq (F := H) (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have same := derived.unique (mass_hasDerivAt seed M 0 time)
  have source := congrArg (fun v : H => inner ℝ (finiteHistory seed time M) v)
    (NativeWindowHistoryOseen.source_equation seed M time)
  rw [inner_add_right (𝕜 := ℝ) (finiteHistory seed time M) (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time),NativeWindowHistoryOseenGap.action_energy] at source
  change inner ℝ (finiteHistory seed time M) (NativeWindowHistoryOseen.rateHistory seed M time)=
    -nu.coeff*gradient M (finiteHistory seed time M)+work seed M time at source
  linarith only [same,source]

theorem gradient_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    gradient M (finiteHistory seed time M)=NativeWindowAugmentedPayment.graphJet seed (modes M) 0 time := by
  have average : (∫ shift,NativeWindowAugmentedPayment.graphSample seed (modes M) (time-shift) ∂averageMeasure)=
      NativeWindowAugmentedPayment.graphJet seed (modes M) 0 time := by
    rw [NativeForwardWindowPairingReadout.density_integral]
    rfl
  apply Eq.trans _ average
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryOseen.history_original seed M time,NativeWindowTraceEndpointWindow.average_interval]
    with shift original support
  rw [original,NativeWindowHistoryOseen.velocityPath,restrict_include]
  exact (NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M) (modes_closed M) nu _ _).symm.trans
    (NativeWindowTraceCutActionPhysical.graph_original seed M (time-shift) (by linarith [support.2]))

theorem source_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    |work seed M time| ≤ (1/2 : ℝ)*NativeWindowFiniteStressUniform.kernelBound 1*(NativeUnifiedCompleteSource.budget seed)^2+
      nu.coeff*NativeWindowAugmentedPayment.graphBudget seed 0 horizon := by
  rw [work_original,gradient_original seed M time inside.1,← Real.norm_eq_abs]
  have bound := norm_add_le ((1/2 : ℝ)*massJet seed M 1 time)
    (nu.coeff*NativeWindowAugmentedPayment.graphJet seed (modes M) 0 time)
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2),Real.norm_of_nonneg nu.coeff_pos.le] at bound
  exact bound.trans ((add_le_add (mul_le_mul_of_nonneg_left (mass_bound seed M 1 time inside.1) (by norm_num))
    (mul_le_mul_of_nonneg_left (NativeWindowAugmentedPayment.graphJet_bound seed (modes M) 0 time horizon inside) nu.coeff_pos.le)).trans_eq (by ring))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    work seed M (step.2.clockAdvance+time)=work step.1 M time :=
  congrArg₂ (fun x y : H => inner ℝ x y)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)
    (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryForcingWork
