import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Graph
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Payment
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.MixedCubic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalMixedWindow
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
open NativeWindowTraceTerminalAverage (stressSquare squareRead squareRead_original)
open NativeWindowTraceGradient (traceStress)
open NativeWindowStressHeatSource (physical)
open NativePhysicalFourier
open NativeWindowConvectionCutoffTrace (correction)
open NativeWindowTraceCutOperator (jointTest)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceEndpointWindow (terminal terminalEnergy)
open NativeWindowAugmentedGradientSource (palinstrophyWindow)
open NativeWindowTraceTerminalPayment (theta theta_positive source_point)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}


theorem mixed_integrable (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (F : Finset IntegerWavevector) :
    Integrable (fun shift => stressSquare seed frame F (sampling-shift)) averageMeasure := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have paid:=(squareRead (traceStress seed frame F)).integrable_comp
    (NativeWindowFiniteGramFourier.pair_integrable seed sampling F i i)
  simpa only [NativeWindowFiniteGramFourier.pairRead,← NativeWindowStressHeatTime.field_original,squareRead_original] using! paid

theorem mixed_average (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (F : Finset IntegerWavevector) :
    (∫ shift,stressSquare seed frame F (sampling-shift) ∂averageMeasure)=
      ∫ point : Torus,(traceStress seed frame F point)^2*traceStress seed sampling F point := by
  have paid (i : Coordinate):=(squareRead (traceStress seed frame F)).integrable_comp
    (NativeWindowFiniteGramFourier.pair_integrable seed sampling F i i)
  have same : stressSquare seed frame F=fun sample => ∑ i : Coordinate,
      squareRead (traceStress seed frame F) (NativeWindowFiniteGramFourier.pairRead F i i (NativeUnifiedCompleteSource.source seed sample)) := by
    funext sample
    simp only [stressSquare,NativeWindowFiniteGramFourier.pairRead,← NativeWindowStressHeatTime.field_original,squareRead_original]
  rw [same,integral_finsetSum Finset.univ (fun i _ => paid i)]
  simp only [(squareRead (traceStress seed frame F)).integral_comp_comm
    (NativeWindowFiniteGramFourier.pair_integrable seed sampling F _ _),← map_sum]
  change squareRead (traceStress seed frame F) (traceStress seed sampling F)=_
  rw [squareRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

theorem source_mixed_average (seed : GeneratedWholeRestartCurrent nu) (cutoff : ℕ) (frame sampling horizon : ℝ)
    (frameInside : frame∈Icc 0 horizon) (sampleInside : sampling∈Icc 0 horizon) :
    (∫ shift,stressSquare seed frame (integerWaveFrequencyCube cutoff) (sampling-shift) ∂averageMeasure)≤
      NativeWindowTraceTerminalCubic.budget seed horizon := by
  rw [mixed_average]
  exact NativeWindowTraceTerminalMixedCubic.source_mixed_bound seed cutoff frame sampling horizon frameInside sampleInside

def energy (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∫ shift,‖coefficients (modes M) (terminal seed frame M F radius (sampling-shift))‖^2 ∂averageMeasure

theorem diagonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    energy seed time time M F radius=terminalEnergy seed time M F radius := rfl

theorem energy_nonnegative (seed : GeneratedWholeRestartCurrent nu) (frame sampling : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : 0≤energy seed frame sampling M F radius := integral_nonneg fun _ => sq_nonneg _

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∃ C : ℝ,0≤C ∧
      ∀ radius≥low,∀ cutoff≥low,∀ M : ℕ,∀ frame∈Icc 0 horizon,∀ sampling∈Icc 0 horizon,
        (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
        energy seed frame sampling M (integerWaveFrequencyCube cutoff) radius≤
          (1+epsilon)*nu.coeff^2*palinstrophyWindow seed M sampling+C := by
  obtain ⟨low,point⟩ := source_point seed horizon nonnegative epsilon positive
  let K:=3*(1+(theta epsilon)⁻¹)
  have K0 : 0≤K := by dsimp only [K]; positivity [theta_positive epsilon positive]
  let C:=max 0 (K*NativeWindowTraceTerminalCubic.budget seed horizon)
  refine ⟨low,C,le_max_left _ _,fun radius above cutoff covered M frame frameInside sampling sampleInside cover => ?_⟩
  let F:=integerWaveFrequencyCube cutoff
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have terminalPaid := (co.comp_memLp' (NativeWindowTraceTerminalGraph.continuous_memLp sampling (terminal seed frame M F radius) (NativeWindowTraceEndpointWindow.terminal_continuous seed frame M F radius) 2)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have palinPaid:=NativeWindowAugmentedGradientSource.palinstrophy_integrable seed M sampling
  have stressPaid:=mixed_integrable seed frame sampling F
  have estimate : ∀ᵐ shift ∂averageMeasure,
      ‖coefficients (modes M) (terminal seed frame M F radius (sampling-shift))‖^2≤
        (1+epsilon)*nu.coeff^2*‖NativeWindowAugmentedGradientSource.palinRead nu M
          (NativeUnheatedSourceQuadraticApprox.physicalSource seed (sampling-shift))‖^2+K*stressSquare seed frame F (sampling-shift) := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    have sample0 : 0 ≤ sampling-shift := by linarith [sampleInside.1]
    have tested:=point radius above cutoff covered (modes M) (modes_zero M) (modes_closed M) frame frameInside
      (NativeWindowTraceAdjoint.value seed M (sampling-shift))
    have stress:=NativeWindowTraceTerminalAverage.stressNorm_square seed frame M F cover (sampling-shift) sample0
    change stressNorm seed frame (modes M) F (NativeWindowTraceAdjoint.value seed M (sampling-shift))^2≤
      3*stressSquare seed frame F (sampling-shift) at stress
    have same : ‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (NativeWindowTraceAdjoint.value seed M (sampling-shift)))‖^2=
        ‖NativeWindowAugmentedGradientSource.palinRead nu M
          (NativeUnheatedSourceQuadraticApprox.physicalSource seed (sampling-shift))‖^2 := by
      rw [NativeWindowAugmentedGradientSource.palinRead_original,
        ← NativeWindowTraceDualWindow.value_load seed M (sampling-shift) sample0]
      exact (real_inner_self_eq_norm_sq _).symm
    rw [same] at tested
    have paid:=mul_le_mul_of_nonneg_left stress (by positivity [theta_positive epsilon positive] : 0≤1+(theta epsilon)⁻¹)
    change ‖coefficients (modes M) (jointTest seed frame (modes M) F radius
      (NativeWindowTraceAdjoint.value seed M (sampling-shift)))‖^2≤_
    exact tested.trans ((add_le_add le_rfl paid).trans_eq (by dsimp only [K,F]; ring))
  have integrated:=integral_mono_ae terminalPaid
    ((palinPaid.const_mul ((1+epsilon)*nu.coeff^2)).add (stressPaid.const_mul K)) estimate
  simp only [Pi.add_apply] at integrated
  rw [integral_add (palinPaid.const_mul _) (stressPaid.const_mul _),integral_const_mul,integral_const_mul] at integrated
  have stressBound:=mul_le_mul_of_nonneg_left
    (source_mixed_average seed cutoff frame sampling horizon frameInside sampleInside) K0
  change energy seed frame sampling M F radius≤(1+epsilon)*nu.coeff^2*palinstrophyWindow seed M sampling+C
  change energy seed frame sampling M F radius≤(1+epsilon)*nu.coeff^2*palinstrophyWindow seed M sampling+
    K*(∫ shift,stressSquare seed frame F (sampling-shift) ∂averageMeasure) at integrated
  exact integrated.trans (add_le_add le_rfl (stressBound.trans (le_max_right _ _)))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem energy_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame sampling : ℝ)
    (frame0 : 0≤frame) (sampling0 : 0 ≤ sampling) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    energy seed (step.2.clockAdvance+frame) (step.2.clockAdvance+sampling) M F radius=
      energy step.1 frame sampling M F radius := by
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
  change ‖coefficients (modes M) (terminal seed (step.2.clockAdvance+frame) M F radius
    (step.2.clockAdvance+sampling-shift))‖^2=_
  rw [add_sub_assoc,NativeWindowTraceEndpointWindow.terminal_next seed step generated frame frame0 M F radius
    (sampling-shift) (by linarith)]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalMixedWindow
