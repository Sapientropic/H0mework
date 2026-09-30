import H0mework.Computation.LoadedADCPacket.Conditional
import H0mework.Probability.Source.ConditionalNextEntropy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def conditionalEntropy (bound : Nat) : ℝ :=
  SourceConditionalNext.conditionalEntropy (historyPMF bound)
    (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound)
    (fun actor => (PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor))

theorem conditionalEntropy_formula (bound : Nat) :
    conditionalEntropy downstreamTechnology downstreamGraph seed bound =
      ∑ actor, (historyPMF bound actor).toReal *
        entropy (conditionalNext downstreamTechnology downstreamGraph seed bound
          (nowPacket downstreamTechnology downstreamGraph seed bound actor)
          (observed_supported _ _ actor ((PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor)))) := rfl

theorem conditionalEntropy_nonnegative (bound : Nat) :
    0 ≤ conditionalEntropy downstreamTechnology downstreamGraph seed bound :=
  SourceConditionalNext.conditionalEntropy_nonnegative _ _ _ _

theorem conditionalEntropy_zero_iff (bound : Nat) :
    conditionalEntropy downstreamTechnology downstreamGraph seed bound = 0 ↔
      ∀ left right : Fin (bound + 1),
        nowPacket downstreamTechnology downstreamGraph seed bound left =
            nowPacket downstreamTechnology downstreamGraph seed bound right →
          nextPacket downstreamTechnology downstreamGraph seed bound left =
            nextPacket downstreamTechnology downstreamGraph seed bound right :=
  SourceConditionalNext.conditionalEntropy_zero_iff _ _ _ _

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
