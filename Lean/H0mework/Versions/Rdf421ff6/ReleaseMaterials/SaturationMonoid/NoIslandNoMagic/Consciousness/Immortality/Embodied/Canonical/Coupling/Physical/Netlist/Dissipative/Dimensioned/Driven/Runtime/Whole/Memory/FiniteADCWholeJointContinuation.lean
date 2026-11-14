import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Runtime.Whole.Memory.FiniteADCWholeJointContinuity

/-! # The existing rooted recursion consumes the complete physical joint current -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {bootInitial : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

theorem step_semiconj :
    Function.Semiconj (fun current : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology => current.plant)
      (fun current => current.step downstreamTechnology downstreamGraph)
      (finiteADCPhysicalDelayedSuccessor
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph)) :=
  fun current => current.step_plant downstreamTechnology downstreamGraph

def after (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology :=
  ((fun current => current.step downstreamTechnology downstreamGraph)^[frames]) seed

theorem after_plant (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    (after downstreamTechnology downstreamGraph seed frames).plant =
      finiteADCPhysicalDelayedCurrentAfter
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph) seed.plant frames :=
  (step_semiconj downstreamTechnology downstreamGraph).iterate_right frames seed

def exposure (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    RootedAccountedUnfolding (FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) :=
  RootedAccountedUnfolding.observe (fun current => .zero (current.step downstreamTechnology downstreamGraph)) seed frames

theorem exposure_frontier (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    (exposure downstreamTechnology downstreamGraph seed frames).frontier =
      [after downstreamTechnology downstreamGraph seed frames] :=
  rootedUnaryObservation_frontier
    (fun current : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology =>
      current.step downstreamTechnology downstreamGraph) seed frames

theorem after_reads_own_snapshot (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    (after downstreamTechnology downstreamGraph seed frames).physicalRead downstreamTechnology downstreamGraph =
      some (some (after downstreamTechnology downstreamGraph seed frames).plant.val.drive) :=
  (after downstreamTechnology downstreamGraph seed frames).physicalRead_received downstreamTechnology downstreamGraph

def elapsed (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) : ℝ :=
  ∑ frame ∈ Finset.range frames,
    (finiteADCPhysicalSwitchTimeAt (after downstreamTechnology downstreamGraph seed frame).plant
      (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
        technology downstreamTechnology downstreamGraph)).value

theorem elapsed_eq_existing (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    elapsed downstreamTechnology downstreamGraph seed frames =
      finiteADCPhysicalDelayedElapsed
        (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
          technology downstreamTechnology downstreamGraph) seed.plant frames := by
  unfold elapsed finiteADCPhysicalDelayedElapsed
  apply Finset.sum_congr rfl
  intro frame _
  rw [after_plant]

theorem no_zeno (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (timeBound : ℝ) :
    ∃ frames : Nat, timeBound < elapsed downstreamTechnology downstreamGraph seed frames := by
  obtain ⟨frames, later⟩ := finiteADCPhysicalDelayedContinuation_no_zeno
    (receiverWholeHardwareProcessingTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
      technology downstreamTechnology downstreamGraph) seed.plant timeBound
  exact ⟨frames, by rw [elapsed_eq_existing]; exact later⟩

theorem arbitrary_finite_horizon
    (seed : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology) (frames : Nat) :
    ∃ current : FiniteADCWholeJointCurrent hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) technology,
      (exposure downstreamTechnology downstreamGraph seed frames).frontier = [current] ∧
      current.physicalRead downstreamTechnology downstreamGraph = some (some current.plant.val.drive) ∧
      ∀ node polarity,
        (current.step downstreamTechnology downstreamGraph).receiverStateAt downstreamTechnology downstreamGraph node polarity 0 =
          current.receiverStateAt downstreamTechnology downstreamGraph node polarity
            (current.memoryEndpointTime downstreamTechnology downstreamGraph) := by
  refine ⟨after downstreamTechnology downstreamGraph seed frames,
    exposure_frontier downstreamTechnology downstreamGraph seed frames,
    after_reads_own_snapshot downstreamTechnology downstreamGraph seed frames, ?_⟩
  exact (after downstreamTechnology downstreamGraph seed frames).step_receiver_memory_no_reset
    downstreamTechnology downstreamGraph

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
