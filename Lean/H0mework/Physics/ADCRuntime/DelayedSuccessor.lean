import H0mework.Physics.ADCRuntime.ProcessingTime
import H0mework.Physics.ADCRuntime.Continuation

/-!
# Physical continuation with source-clocked processing delay

Feedback reads the stored ADC snapshot once. The old drive continues through
a configured finite number of ticks, and its actual state at the switch is
the next initial. Generic iteration and rooted exposure consume this one
step; zero processing ticks recovers the previously certified runtime.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Units.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def finiteADCPhysicalDelayedSuccessor
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  startFiniteADCPhysicalRuntime hardware
    (finiteADCPhysicalDelayedEndpoint current processingTicks)
    (finiteADCPhysicalFeedback current)

@[simp] theorem finiteADCPhysicalDelayedSuccessor_zero
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    finiteADCPhysicalDelayedSuccessor 0 current = finiteADCPhysicalSuccessor current := rfl

theorem finiteADCPhysicalDelayedSuccessor_no_reset
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    finiteADCPhysicalStateAt (finiteADCPhysicalDelayedSuccessor processingTicks current) 0 =
      finiteADCPhysicalStateAt current (finiteADCPhysicalSwitchTimeAt current processingTicks) :=
  drivenTotalPortState_initial_exact _ _ _ _

theorem finiteADCPhysicalDelayedSuccessor_snapshot_feedback
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    (finiteADCPhysicalDelayedSuccessor processingTicks current).val.drive =
      (match finiteADCPhysicalReceived current with
       | some snapshot => fun channel => !(snapshot channel)
       | none => uniformBinaryDrive false) := rfl

theorem finiteADCPhysicalDelayedSuccessor_feedback_exact
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    (finiteADCPhysicalDelayedSuccessor processingTicks current).val.drive =
      fun channel => !(current.val.drive channel) :=
  finiteADCPhysicalFeedback_exact current

theorem finiteADCPhysicalDelayedSuccessor_regenerates_sample
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      (finiteADCPhysicalCurrentSource (finiteADCPhysicalDelayedSuccessor processingTicks current))
      (finiteADCPhysicalDelayedSuccessor processingTicks current).val.drive :=
  finiteADCPhysicalCurrent_generates_receipt _

def finiteADCPhysicalDelayedCurrentAfter
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  ((finiteADCPhysicalDelayedSuccessor processingTicks)^[frames]) seed

theorem finiteADCPhysicalDelayedCurrentAfter_succ
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    finiteADCPhysicalDelayedCurrentAfter processingTicks seed (frames + 1) =
      finiteADCPhysicalDelayedSuccessor processingTicks
        (finiteADCPhysicalDelayedCurrentAfter processingTicks seed frames) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem finiteADCPhysicalDelayedCurrentAfter_zero_delay
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    finiteADCPhysicalDelayedCurrentAfter 0 seed frames =
      finiteADCPhysicalCurrentAfter seed frames := rfl

def finiteADCPhysicalDelayedExposure
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    RootedAccountedUnfolding (FiniteADCPhysicalRuntimeCurrent hardware) :=
  RootedAccountedUnfolding.observe
    (fun current => .zero (finiteADCPhysicalDelayedSuccessor processingTicks current)) seed frames

theorem finiteADCPhysicalDelayedExposure_frontier
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    (finiteADCPhysicalDelayedExposure processingTicks seed frames).frontier =
      [finiteADCPhysicalDelayedCurrentAfter processingTicks seed frames] :=
  rootedUnaryObservation_frontier (finiteADCPhysicalDelayedSuccessor processingTicks) seed frames

def finiteADCPhysicalDelayedElapsed
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) : ℝ :=
  ∑ frame ∈ Finset.range frames,
    (finiteADCPhysicalSwitchTimeAt
      (finiteADCPhysicalDelayedCurrentAfter processingTicks seed frame) processingTicks).value

theorem finiteADCPhysicalDelayedElapsed_lower_bound
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (frames : Nat) :
    (frames : ℝ) *
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value ≤
      finiteADCPhysicalDelayedElapsed processingTicks seed frames := by
  calc
    _ = ∑ _frame ∈ Finset.range frames,
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value := by simp
    _ ≤ _ := Finset.sum_le_sum (fun frame _ =>
      le_trans (finiteADCPhysicalCurrent_duration_ge_tick _)
        (finiteADCPhysicalSwitchTimeAt_ge_sample
          (finiteADCPhysicalDelayedCurrentAfter processingTicks seed frame) processingTicks))

theorem finiteADCPhysicalDelayedContinuation_no_zeno
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (processingTicks : Nat) (seed : FiniteADCPhysicalRuntimeCurrent hardware) (timeBound : ℝ) :
    ∃ frames : Nat, timeBound < finiteADCPhysicalDelayedElapsed processingTicks seed frames := by
  let tick := (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
    hardware.clockCode).value
  have positive : 0 < tick :=
    finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  obtain ⟨frames, enough⟩ := exists_nat_gt (timeBound / tick)
  have scaled := mul_lt_mul_of_pos_right enough positive
  rw [div_mul_cancel₀ _ (ne_of_gt positive)] at scaled
  exact ⟨frames, lt_of_lt_of_le scaled
    (finiteADCPhysicalDelayedElapsed_lower_bound processingTicks seed frames)⟩

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
