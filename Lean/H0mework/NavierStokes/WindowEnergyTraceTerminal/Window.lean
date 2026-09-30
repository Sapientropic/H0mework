import H0mework.NavierStokes.WindowEnergyTraceEndpoint.Window
import H0mework.NavierStokes.WindowEnergyTraceTerminal.Payment

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWholeH1Mixed NativeWindowOperatorGreen
open NativeWindowTraceTerminalSynthesis (cap cap_positive)
open NativeWindowTraceTerminalOperator (stressNorm joint_bound)
open NativeWindowTraceTerminalAverage (stressSquare)
open NativeWindowConvectionCutoffTrace (correction)
open NativeWindowTraceCutOperator (jointTest)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceEndpointWindow (terminal terminalEnergy)
open NativeWindowAugmentedGradientSource (palinstrophyWindow)
open NativeWindowTraceTerminalPayment (theta theta_positive source_point)
noncomputable section
variable {nu : Viscosity}

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∃ C : ℝ,0≤C ∧
      ∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,∀ time∈Icc 0 horizon,
        (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
        terminalEnergy seed time M (integerWaveFrequencyCube cutoff) radius≤
          (1+epsilon)*nu.coeff^2*palinstrophyWindow seed M time+C := by
  obtain ⟨low,point⟩ := source_point seed horizon nonnegative epsilon positive
  let K:=3*(1+(theta epsilon)⁻¹)
  have K0 : 0≤K := by dsimp only [K]; positivity [theta_positive epsilon positive]
  let C:=max 0 (K*NativeWindowTraceTerminalCubic.budget seed horizon)
  refine ⟨low,C,le_max_left _ _,fun radius above cutoff covered M time inside cover => ?_⟩
  let F:=integerWaveFrequencyCube cutoff
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have terminalPaid := (co.comp_memLp' (NativeWindowTraceEndpointWindow.terminal_memLp seed time M F radius 2)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have palinPaid:=NativeWindowAugmentedGradientSource.palinstrophy_integrable seed M time
  have stressPaid:=NativeWindowTraceTerminalAverage.stressSquare_integrable seed time F
  have estimate : ∀ᵐ shift ∂averageMeasure,
      ‖coefficients (modes M) (terminal seed time M F radius (time-shift))‖^2≤
        (1+epsilon)*nu.coeff^2*‖NativeWindowAugmentedGradientSource.palinRead nu M
          (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2+K*stressSquare seed time F (time-shift) := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    have sample0 : 0≤time-shift := by linarith [inside.1]
    have tested:=point radius above cutoff covered (modes M) (modes_zero M) (modes_closed M) time inside
      (NativeWindowTraceAdjoint.value seed M (time-shift))
    have stress:=NativeWindowTraceTerminalAverage.stressNorm_square seed time M F cover (time-shift) sample0
    change stressNorm seed time (modes M) F (NativeWindowTraceAdjoint.value seed M (time-shift))^2≤
      3*stressSquare seed time F (time-shift) at stress
    have same : ‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (NativeWindowTraceAdjoint.value seed M (time-shift)))‖^2=
        ‖NativeWindowAugmentedGradientSource.palinRead nu M
          (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2 := by
      rw [NativeWindowAugmentedGradientSource.palinRead_original,
        ← NativeWindowTraceDualWindow.value_load seed M (time-shift) sample0]
      exact (real_inner_self_eq_norm_sq _).symm
    rw [same] at tested
    have paid:=mul_le_mul_of_nonneg_left stress (by positivity [theta_positive epsilon positive] : 0≤1+(theta epsilon)⁻¹)
    change ‖coefficients (modes M) (jointTest seed time (modes M) F radius
      (NativeWindowTraceAdjoint.value seed M (time-shift)))‖^2≤_
    exact tested.trans ((add_le_add le_rfl paid).trans_eq (by dsimp only [K,F]; ring))
  have integrated:=integral_mono_ae terminalPaid
    ((palinPaid.const_mul ((1+epsilon)*nu.coeff^2)).add (stressPaid.const_mul K)) estimate
  simp only [Pi.add_apply] at integrated
  rw [integral_add (palinPaid.const_mul _) (stressPaid.const_mul _),integral_const_mul,integral_const_mul] at integrated
  have stressBound:=mul_le_mul_of_nonneg_left
    (NativeWindowTraceTerminalAverage.source_stressSquare seed time horizon inside cutoff) K0
  change terminalEnergy seed time M F radius≤(1+epsilon)*nu.coeff^2*palinstrophyWindow seed M time+C
  change terminalEnergy seed time M F radius≤(1+epsilon)*nu.coeff^2*palinstrophyWindow seed M time+
    K*(∫ shift,stressSquare seed time F (time-shift) ∂averageMeasure) at integrated
  exact integrated.trans (add_le_add le_rfl (stressBound.trans (le_max_right _ _)))


def loss (nu : Viscosity) : ℝ := (1+(NativeWindowTraceAdjointGap.factor nu)^2)/2

theorem loss_range (nu : Viscosity) : 0<loss nu ∧ loss nu<1 := by
  have lower:=NativeWindowTraceAdjointGap.factor_positive nu
  have upper:=NativeWindowTraceAdjointGap.factor_lt_one nu
  constructor
  · unfold loss; positivity
  · unfold loss; nlinarith only [lower,upper]

theorem source_strict_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
      NativeWindowTraceEndpointWindow.energy seed time M (integerWaveFrequencyCube cutoff) radius≤
        loss nu*nu.coeff^2*palinstrophyWindow seed M time+C ∧
      ‖coefficients (modes M) (NativeWindowTraceEndpointWindow.window seed time M (integerWaveFrequencyCube cutoff) radius)‖^2≤
        loss nu*nu.coeff^2*palinstrophyWindow seed M time+C := by
  let f:=NativeWindowTraceAdjointGap.factor nu
  have f0 : 0<f := NativeWindowTraceAdjointGap.factor_positive nu
  have f1 : f<1 := NativeWindowTraceAdjointGap.factor_lt_one nu
  let epsilon:=(1-f^2)/2
  have positive : 0<epsilon := by dsimp only [epsilon]; nlinarith only [f0,f1]
  obtain ⟨low,C,C0,paid⟩ := source_bound seed horizon nonnegative epsilon positive
  refine ⟨low,f^2*C,mul_nonneg (sq_nonneg _) C0,fun radius above cutoff covered M time inside cover => ?_⟩
  have terminalBound:=mul_le_mul_of_nonneg_left (paid radius above cutoff covered M time inside cover) (sq_nonneg f)
  have fraction : f^2*(1+epsilon)≤loss nu := by
    change f^2*(1+(1-f^2)/2)≤(1+f^2)/2
    nlinarith only [sq_nonneg (1-f^2)]
  have coefficient:=mul_le_mul_of_nonneg_right fraction (mul_nonneg (sq_nonneg nu.coeff)
    (NativeWindowAugmentedGradientSource.palinstrophy_nonnegative seed M time))
  have bound : f^2*terminalEnergy seed time M (integerWaveFrequencyCube cutoff) radius≤
      loss nu*nu.coeff^2*palinstrophyWindow seed M time+f^2*C := by
    nlinarith only [terminalBound,coefficient]
  exact ⟨(NativeWindowTraceEndpointWindow.source_contraction seed time M (integerWaveFrequencyCube cutoff) radius).trans bound,
    (NativeWindowTraceEndpointWindow.source_window_bound seed time M (integerWaveFrequencyCube cutoff) radius).trans bound⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalWindow
