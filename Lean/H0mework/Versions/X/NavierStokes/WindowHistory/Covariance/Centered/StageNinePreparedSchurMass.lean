import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedSourceIdentity
import H0mework.Versions.X.NavierStokes.WindowHistory.ForcingWork
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.TemporalControl

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedSchurMass
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryForcingWork (massJet massForm)
noncomputable section
variable {nu : Viscosity}

theorem value_mass_total (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) :
    ‖coefficients (modes M) (NativeWindowTraceAdjoint.value seed M sample)‖ ≤
      NativeUnifiedCompleteSource.budget seed := by
  by_cases nonnegative : 0 ≤ sample
  · exact NativeWindowTraceAdjoint.value_mass_bound seed M sample nonnegative
  · have before : sample ≤ 0 := le_of_not_ge nonnegative
    have same : NativeWindowTraceAdjoint.value seed M sample =
        NativeWindowTraceAdjoint.value seed M 0 := by
      simp only [NativeWindowTraceAdjoint.value,
        NativeWindowHierarchyPairWindow.state_before seed sample before]
    rw [same]
    exact NativeWindowTraceAdjoint.value_mass_bound seed M 0 le_rfl

theorem mass_jet_total (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖massJet seed M order time‖ ≤
      NativeWindowFiniteStressUniform.kernelBound order*(NativeUnifiedCompleteSource.budget seed)^2 := by
  rw [massJet,NativeWindowHierarchyPairWindow.window_original]
  have point (sample : ℝ) (inside : sample ∈ Set.uIoc (time+1) (time+2)) :
      ‖NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample •
        NativeWindowHierarchyPairWindow.pair seed (massForm M) sample‖ ≤
        NativeWindowFiniteStressUniform.kernelBound order*(NativeUnifiedCompleteSource.budget seed)^2 := by
    rw [norm_smul,NativeWindowHistoryForcingWork.mass_sample,
      Real.norm_of_nonneg (sq_nonneg _)]
    simp only [NativeUnheatedStressPairEvolution.kernelWeight,zero_add]
    exact mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample))
      (pow_le_pow_left₀ (norm_nonneg _) (value_mass_total seed M sample) 2)
      (sq_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have paid := intervalIntegral.norm_integral_le_of_norm_le_const point
  simpa only [show time+2-(time+1)=(1 : ℝ) by ring,abs_one,mul_one] using paid

theorem history_mass_total (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖NativeWindowTraceWholeHistory.finiteHistory seed time M‖^2 ≤
      NativeWindowHistorySchurTemporalControl.massBudget seed := by
  rw [NativeWindowHistoryForcingWork.mass_original]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (mass_jet_total seed M 0 time))

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedSchurMass
