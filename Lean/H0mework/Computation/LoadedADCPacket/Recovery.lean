import H0mework.Computation.LoadedADCPacket.Conditional
import H0mework.Probability.Recovery.Refinement

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def jointPacket (bound : Nat) (actor : Fin (bound + 1)) :=
  (nowPacket downstreamTechnology downstreamGraph seed bound actor,
    nextPacket downstreamTechnology downstreamGraph seed bound actor)

theorem next_error_zero (bound : Nat) :
    error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound)
      (sampleTask downstreamTechnology downstreamGraph seed bound) headerDecoder = 0 := by
  simp only [error, sampleTask_eq_decode_next, sub_self, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]

theorem joint_error_zero (bound : Nat) :
    error (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
      (sampleTask downstreamTechnology downstreamGraph seed bound) (headerDecoder ∘ Prod.snd) = 0 := by
  exact next_error_zero downstreamTechnology downstreamGraph seed bound

theorem joint_residual_zero (bound : Nat) :
    residual (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound)) = 0 := by
  have boundError := optimal_lower_bound (historyPMF bound)
    (jointPacket downstreamTechnology downstreamGraph seed bound)
    (sampleTask downstreamTechnology downstreamGraph seed bound) (headerDecoder ∘ Prod.snd)
  rw [optimal_attains, joint_error_zero] at boundError
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm boundError (sq_nonneg _)))

theorem joint_transfer_exact (bound : Nat) :
    pullback (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
      (transfer (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound))) =
      taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound) := by
  have retained := IsometricRetainedTransfer.pullback_transfer_add_residual
    (pullback (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound))
    (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound))
  change pullback (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
    (transfer (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound))) +
    residual (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound)) = _ at retained
  rw [joint_residual_zero, add_zero] at retained
  exact retained

theorem current_to_joint_gain (bound : Nat) :
    error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (sampleTask downstreamTechnology downstreamGraph seed bound)
        (optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
          (sampleTask downstreamTechnology downstreamGraph seed bound)) -
      error (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
        (sampleTask downstreamTechnology downstreamGraph seed bound)
        (optimalDecoder (historyPMF bound) (jointPacket downstreamTechnology downstreamGraph seed bound)
          (sampleTask downstreamTechnology downstreamGraph seed bound)) =
      ∑ actor, (historyPMF bound actor).toReal * sampleVariance downstreamTechnology downstreamGraph seed bound actor := by
  rw [optimal_attains, optimal_attains, joint_residual_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, original_residual_variance]

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
