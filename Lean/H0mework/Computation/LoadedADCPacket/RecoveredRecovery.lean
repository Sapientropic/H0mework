import H0mework.Computation.LoadedADCPacket.RecoveredNext
import H0mework.Computation.LoadedADCPacket.RecipientConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recovered

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

local instance readoutMeasurable : MeasurableSpace
    (Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) := ⊤

local instance readoutSingletons : MeasurableSingletonClass
    (Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  ⟨fun _ => trivial⟩

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def taskDecoder
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ)
    (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  (predictCurrent downstreamTechnology downstreamGraph value).elim 0 task

variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def nextTask (bound : Nat)
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ)
    (actor : Fin (bound + 1)) : ℂ :=
  task (loadedStep downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed actor.val))

theorem actual_next_recovered (bound : Nat)
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ)
    (actor : Fin (bound + 1)) :
    taskDecoder downstreamTechnology downstreamGraph task (observation downstreamTechnology downstreamGraph seed bound actor) =
      nextTask downstreamTechnology downstreamGraph seed bound task actor := by
  unfold taskDecoder observation
  rw [predictCurrent_source]
  rfl

theorem next_error_zero (bound : Nat)
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ) :
    error (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound)
      (nextTask downstreamTechnology downstreamGraph seed bound task)
      (taskDecoder downstreamTechnology downstreamGraph task) = 0 := by
  simp only [error, actual_next_recovered, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

theorem next_residual_zero (bound : Nat)
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ) :
    residual (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (nextTask downstreamTechnology downstreamGraph seed bound task)) = 0 := by
  have boundError := optimal_lower_bound (historyPMF bound)
    (observation downstreamTechnology downstreamGraph seed bound)
    (nextTask downstreamTechnology downstreamGraph seed bound task)
    (taskDecoder downstreamTechnology downstreamGraph task)
  rw [optimal_attains, next_error_zero] at boundError
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm boundError (sq_nonneg _)))

theorem next_transfer_exact (bound : Nat)
    (task : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℂ) :
    pullback (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound)
      (transfer (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (nextTask downstreamTechnology downstreamGraph seed bound task))) =
      taskValue (historyPMF bound) (nextTask downstreamTechnology downstreamGraph seed bound task) := by
  have retained := IsometricRetainedTransfer.pullback_transfer_add_residual
    (pullback (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound))
    (taskValue (historyPMF bound) (nextTask downstreamTechnology downstreamGraph seed bound task))
  change _ + residual (historyPMF bound) (observation downstreamTechnology downstreamGraph seed bound)
    (taskValue (historyPMF bound) (nextTask downstreamTechnology downstreamGraph seed bound task)) = _ at retained
  rw [next_residual_zero, add_zero] at retained
  exact retained

theorem next_information_zero (bound : Nat) :
    SourceConditionalNext.conditionalEntropy (historyPMF bound)
      (observation downstreamTechnology downstreamGraph seed bound)
      (nextPacket downstreamTechnology downstreamGraph seed bound)
      (fun actor => (PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor)) = 0 := by
  apply (SourceConditionalNext.conditionalEntropy_zero_iff _ _ _ _).mpr
  intro left right same
  have states := sourceRead_injective same
  exact congrArg (fun current => (loadedStep downstreamTechnology downstreamGraph current).packet) states

end
end FiniteADCWholeJointCurrent.Information.Packet.Recovered
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
