import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Mean
import H0mework.Versions.X.NavierStokes.WindowHistory.SpatialWords

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationFirstJet
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryAdjointSpatialHalf (moment multiplier_bound)
open NativeWindowAugmentedGradient (derivative derivative_apply)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
open NativeWindowHistorySpatialWords (fiber)
open NativeUnheatedSexticLatticePower (radical)
noncomputable section
variable {nu : Viscosity}

theorem derivative_moment (F : Finset IntegerWavevector) (zero : 0∉F) (closed : FiniteModeNegClosed F)
    (j : Coordinate) (v : physicalSpace F) :
    moment F 1 (derivative F zero closed j v) ≤ (2*Real.pi)^2*moment F 3 v := by
  have frequency (k : IntegerWavevector) : radical k^2*‖NativePhysicalGradient.multiplier k j‖^2 ≤
      (2*Real.pi)^2*radical k^6 := by
    have paid:=pow_le_pow_left₀ (norm_nonneg _) (multiplier_bound k j) 2
    rw [mul_pow,← pow_mul] at paid
    exact (mul_le_mul_of_nonneg_left paid (sq_nonneg (radical k))).trans_eq (by ring)
  rw [NativeWindowHistoryAdjointSpatialHalf.moment_original,NativeWindowHistoryAdjointSpatialHalf.moment_original,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  simp only [derivative_apply,Pi.smul_apply,norm_smul,mul_pow,← Finset.mul_sum]
  have paid:=mul_le_mul_of_nonneg_right (frequency k)
    (Finset.sum_nonneg fun i (_ : i∈(Finset.univ : Finset Coordinate)) => sq_nonneg ‖v.1 k i‖)
  simpa only [mul_pow,mul_assoc] using paid

def firstJet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) (time : ℝ) : physicalSpace (modes M) :=
  derivative (modes M) (modes_zero M) (modes_closed M) j (physicalJet seed M order time)

theorem firstJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) (time : ℝ) :
    HasDerivAt (firstJet seed M order j) (firstJet seed M (order+1) j time) time :=
  (LinearMap.toContinuousLinearMap (NativeWindowStageNineWords.spatialGenerator (modes M) (modes_zero M) (modes_closed M) j)).hasFDerivAt.comp_hasDerivAt time
    (NativeWindowHistoryMeanPhysicalJet.physicalJet_hasDerivAt seed M order time)

theorem firstJet_continuous (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) :
    Continuous (firstJet seed M order j) := continuous_iff_continuousAt.mpr fun t => (firstJet_hasDerivAt seed M order j t).continuousAt

theorem include_firstJet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (firstJet seed M order j time)=
      fiber M [j] (includeCLM (modes M) (modes_closed M) (physicalJet seed M order time)) :=
  (NativeWindowHistoryOseen.lift_included M (LinearMap.toContinuousLinearMap
    (NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) [j])) (physicalJet seed M order time)).symm

theorem source_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (firstJet seed M 0 j time)=
      fiber M [j] (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)) := by
  have base:=(congrArg (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistoryMeanPhysicalJet.physicalJet_zero seed M time)).trans
      (NativeWindowHistoryMeanPhysicalJet.include_mean seed M time)
  exact (include_firstJet seed M 0 j time).trans (congrArg (fiber M [j]) base)

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  (2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed order horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    0 ≤ budget seed order horizon := by
  unfold budget NativeWindowSobolevVelocity.budget
  positivity

theorem firstJet_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (M : ℕ) (j : Coordinate) (time : ℝ) (inside : time∈Icc 0 horizon) :
    moment (modes M) 1 (firstJet seed M order j time) ≤ budget seed order horizon :=
  (derivative_moment (modes M) (modes_zero M) (modes_closed M) j (physicalJet seed M order time)).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryCreationMean.mean_moment seed order horizon M time inside) (sq_nonneg _))

theorem source (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ M (j : Coordinate) time,time∈Icc 0 horizon → moment (modes M) 1 (firstJet seed M order j time) ≤ B :=
  ⟨budget seed order horizon,budget_nonnegative seed order horizon,fun M j time inside => firstJet_bound seed order horizon M j time inside⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem firstJet_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    firstJet seed M order j (step.2.clockAdvance+time)=firstJet step.1 M order j time :=
  congrArg (derivative (modes M) (modes_zero M) (modes_closed M) j)
    (NativeWindowHistoryMeanPhysicalJet.physicalJet_next seed M order step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationFirstJet
