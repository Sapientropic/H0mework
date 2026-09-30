import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.FirstJet
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.CreationEnergy
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CausalEnergy

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalFirstResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (gradient)
open NativeWholeH1Mixed (modes modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryCreationFirstJet (firstJet firstJet_continuous)
open NativeWindowHistoryCausalPassivity (creationResponse)
open NativeWindowHistoryAdjointSpatialHalf (moment)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def driver (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) (t : ℝ) : wholePhysical :=
  includeCLM (modes M) (modes_closed M) (firstJet seed M order j t)

theorem driver_continuous (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate) :
    Continuous (driver seed M order j) :=
  (includeCLM (modes M) (modes_closed M)).continuous.comp (firstJet_continuous seed M order j)

def response (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate)
    (a B : ℝ) (aB : a≤B) : ℝ → H :=
  creationResponse seed M (driver seed M order j) (driver_continuous seed M order j) a B aB

theorem driver_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) :
    driver seed M 0 j=NativeWindowHistoryAllOrderWord.value seed M [j] :=
  funext fun t => NativeWindowHistoryCreationFirstJet.source_original seed M j t

private theorem response_congr (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v w : ℝ → wholePhysical) (vc : Continuous v) (wc : Continuous w)
    (same : v=w) (a B : ℝ) (aB : a≤B) :
    creationResponse seed M v vc a B aB=creationResponse seed M w wc a B aB := by
  subst w
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem response_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate)
    (a B : ℝ) (aB : a≤B) : response seed M 0 j a B aB=NativeWindowHistoryAllOrderCausal.created seed M [j] a B aB :=
  response_congr seed M _ _ _ _ (driver_original seed M j) a B aB

theorem source (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      ‖response seed M order j a horizon start.2 b‖^2+
        nu.coeff*(∫t in a..b,gradient M (response seed M order j a horizon start.2 t))≤C := by
  obtain ⟨C,C0,energy⟩:=NativeWindowHistoryCausalCreationEnergy.source_energy seed horizon
  obtain ⟨D,D0,input⟩:=NativeWindowHistoryCreationFirstJet.source seed order horizon
  refine ⟨C*(horizon*D),mul_nonneg C0 (mul_nonneg nonnegative D0),?_⟩
  intro M j a start b inside
  have paid:=energy M (firstJet seed M order j) (firstJet_continuous seed M order j) a start b inside
  have integrable:=((NativeWindowHistoryCausalCreationEnergy.moment_continuous M 1).comp
    (firstJet_continuous seed M order j)).intervalIntegrable (μ := volume) a b
  have bound:=intervalIntegral.integral_mono_on inside.1 integrable (intervalIntegrable_const (c := D))
    (fun t ht => input M j t ⟨start.1.trans ht.1,ht.2.trans inside.2⟩)
  rw [intervalIntegral.integral_const,smul_eq_mul] at bound
  have full:=bound.trans (mul_le_mul_of_nonneg_right (by linarith [start.1,inside.2] : b-a≤horizon) D0)
  exact paid.trans (mul_le_mul_of_nonneg_left full C0)

theorem source_first_word (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      ‖NativeWindowHistoryAllOrderCausal.created seed M [j] a horizon start.2 b‖^2+
        nu.coeff*(∫t in a..b,gradient M (NativeWindowHistoryAllOrderCausal.created seed M [j] a horizon start.2 t))≤C := by
  obtain ⟨C,C0,paid⟩:=source seed 0 horizon nonnegative
  exact ⟨C,C0,fun M j a start b inside => by simpa only [response_original] using paid M j a start b inside⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem response_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (j : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    response seed M order j (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t)=response step.1 M order j a B aB t :=
  NativeWindowHistoryCausalResponseNext.creationResponse_next seed M step generated
    (driver seed M order j) (driver step.1 M order j) (driver_continuous seed M order j)
    (driver_continuous step.1 M order j) a B aB a0
    (fun s hs => congrArg (includeCLM (modes M) (modes_closed M))
      (NativeWindowHistoryCreationFirstJet.firstJet_next seed M order j step generated s (a0.trans hs.1))) inside

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalFirstResponse
