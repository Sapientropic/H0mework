import H0mework.Physics.ADCRuntime.Successor
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Finite physical continuation without reset or a completed future

Iteration and finite provenance exposure reuse existing generic engines.
Every frame consumes at least one tick of the unchanged physical clock, so
arbitrarily many frames cannot accumulate in a bounded physical time.
The packet header width is still source-relative; a uniform hardware counter
bound is a separate obligation, not implied by preserving the clock code.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Units.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def finiteADCPhysicalCurrentAfter
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  (finiteADCPhysicalSuccessor^[steps]) seed

@[simp] theorem finiteADCPhysicalCurrentAfter_zero
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) :
    finiteADCPhysicalCurrentAfter seed 0 = seed := rfl

theorem finiteADCPhysicalCurrentAfter_succ
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    finiteADCPhysicalCurrentAfter seed (steps + 1) =
      finiteADCPhysicalSuccessor (finiteADCPhysicalCurrentAfter seed steps) :=
  Function.iterate_succ_apply' _ _ _

/-- The next frame is physically continuous at its local time origin. -/
theorem finiteADCPhysicalContinuation_no_reset
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    finiteADCPhysicalStateAt (finiteADCPhysicalCurrentAfter seed (steps + 1)) 0 =
      finiteADCPhysicalEndpoint (finiteADCPhysicalCurrentAfter seed steps) := by
  rw [finiteADCPhysicalCurrentAfter_succ]
  exact finiteADCPhysicalSuccessor_no_reset _

theorem finiteADCPhysicalContinuation_receives
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    finiteADCPhysicalReceived (finiteADCPhysicalCurrentAfter seed steps) =
      some (finiteADCPhysicalCurrentAfter seed steps).val.drive :=
  finiteADCPhysicalReceived_exact _

theorem finiteADCPhysicalContinuation_regenerates_sample
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      (finiteADCPhysicalCurrentSource (finiteADCPhysicalCurrentAfter seed steps))
      (finiteADCPhysicalCurrentAfter seed steps).val.drive :=
  finiteADCPhysicalCurrent_generates_receipt _

def finiteADCPhysicalExposure
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    RootedAccountedUnfolding (FiniteADCPhysicalRuntimeCurrent hardware) :=
  RootedAccountedUnfolding.observe
    (fun current => .zero (finiteADCPhysicalSuccessor current)) seed steps

/-- Readout alignment of the existing unary unfolding and iterate engines. -/
theorem rootedUnaryObservation_frontier
    {State : Type} (step : State → State) (seed : State) (steps : Nat) :
    (RootedAccountedUnfolding.observe (fun current => .zero (step current)) seed steps).frontier =
      [(step^[steps]) seed] := by
  induction steps with
  | zero => rfl
  | succ steps alignment =>
      rw [RootedAccountedUnfolding.observe_succ,
        RootedAccountedUnfolding.frontier_advance, alignment]
      change [step ((step^[steps]) seed)] = [(step^[steps + 1]) seed]
      rw [Function.iterate_succ_apply']

theorem finiteADCPhysicalExposure_frontier_eq_current
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    (finiteADCPhysicalExposure seed steps).frontier =
      [finiteADCPhysicalCurrentAfter seed steps] :=
  rootedUnaryObservation_frontier finiteADCPhysicalSuccessor seed steps

theorem finiteADCPhysicalExposure_generated_frontier
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    (finiteADCPhysicalExposure seed (steps + 1)).frontier =
      (finiteADCPhysicalExposure seed steps).frontier.flatMap
        (fun current => [finiteADCPhysicalSuccessor current]) :=
  RootedAccountedUnfolding.frontier_advance _ _

theorem finiteADCPhysicalExposure_frontier_nonempty
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    (finiteADCPhysicalExposure seed steps).frontier ≠ [] :=
  RootedAccountedUnfolding.frontier_ne_nil _

/-- Each exposed leaf has its own physically joined, newly compiled continuation. -/
theorem finiteADCPhysicalExposure_every_leaf_continues
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat)
    (current : FiniteADCPhysicalRuntimeCurrent hardware)
    (exposed : current ∈ (finiteADCPhysicalExposure seed steps).frontier) :
    ∃ next : FiniteADCPhysicalRuntimeCurrent hardware,
      next = finiteADCPhysicalSuccessor current ∧
      finiteADCPhysicalStateAt next 0 = finiteADCPhysicalEndpoint current ∧
      finiteADCPhysicalReceived next = some next.val.drive ∧
      SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
        (finiteADCPhysicalCurrentSource next) next.val.drive := by
  have sameCurrent : current = finiteADCPhysicalCurrentAfter seed steps := by
    simpa only [finiteADCPhysicalExposure_frontier_eq_current, List.mem_singleton] using exposed
  subst current
  exact ⟨finiteADCPhysicalSuccessor _, rfl,
    finiteADCPhysicalSuccessor_no_reset _,
    finiteADCPhysicalReceived_exact _, finiteADCPhysicalSuccessor_generates_receipt _⟩

/-- Elapsed time is a readout of generated frames, not an installed future table. -/
def finiteADCPhysicalElapsed
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) : ℝ :=
  ∑ step ∈ Finset.range steps,
    (finiteADCPhysicalCurrentAfter seed step).val.executedDuration.value

theorem finiteADCPhysicalElapsed_lower_bound
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (steps : Nat) :
    (steps : ℝ) *
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value ≤
      finiteADCPhysicalElapsed seed steps := by
  calc
    _ = ∑ _step ∈ Finset.range steps,
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value := by simp
    _ ≤ _ := Finset.sum_le_sum
      (fun step _ => finiteADCPhysicalCurrent_duration_ge_tick
        (finiteADCPhysicalCurrentAfter seed step))

/-- No finite physical time can contain all generated frames. -/
theorem finiteADCPhysicalContinuation_no_zeno
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (timeBound : ℝ) :
    ∃ steps : Nat, timeBound < finiteADCPhysicalElapsed seed steps := by
  let tick := (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
    hardware.clockCode).value
  have positive : 0 < tick :=
    finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  obtain ⟨steps, enough⟩ := exists_nat_gt (timeBound / tick)
  have scaled := mul_lt_mul_of_pos_right enough positive
  rw [div_mul_cancel₀ _ (ne_of_gt positive)] at scaled
  exact ⟨steps, lt_of_lt_of_le scaled (finiteADCPhysicalElapsed_lower_bound seed steps)⟩

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
