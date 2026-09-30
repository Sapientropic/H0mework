import H0mework.Computation.LoadedADCPacket.RecoveredRecovery

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recovered

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def programCharge (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    ℝ × ℝ × ℝ :=
  (recoverCurrent value).elim 0 (AccountAction.phaseCharge downstreamTechnology downstreamGraph)

theorem programCharge_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    programCharge downstreamTechnology downstreamGraph (sourceRead current) =
      AccountAction.phaseCharge downstreamTechnology downstreamGraph current := by
  rw [programCharge, recoverCurrent_source]
  rfl

theorem program_energy_balance (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    (predictCurrent downstreamTechnology downstreamGraph (sourceRead current)).elim 0
        (fun next => (jointStoredEnergy next).value) -
      (recoverCurrent (sourceRead current)).elim 0 (fun restored => (jointStoredEnergy restored).value) =
    (programCharge downstreamTechnology downstreamGraph (sourceRead current)).2.1 -
      (programCharge downstreamTechnology downstreamGraph (sourceRead current)).2.2 := by
  rw [predictCurrent_source, recoverCurrent_source, programCharge_source]
  exact loadedStep_energy_balance downstreamTechnology downstreamGraph current

theorem material_frontier (material : RootedAccountedUnfolding
    (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) :
    (material.frontier.map sourceRead).map (predictCurrent downstreamTechnology downstreamGraph) =
      (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph) material).frontier.map some := by
  rw [SourceAccountedAction.occurrenceUpdate, RootedAccountedUnfolding.frontier_advance]
  change _ = (material.frontier.flatMap
    (pure ∘ loadedStep downstreamTechnology downstreamGraph)).map some
  rw [List.flatMap_pure_eq_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro current _
  exact predictCurrent_source downstreamTechnology downstreamGraph current

theorem material_charge (material : RootedAccountedUnfolding
    (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) :
    RootedAccountedUnfolding.SourceCharge.tally (AccountAction.phaseCharge downstreamTechnology downstreamGraph)
      (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph) material) =
    RootedAccountedUnfolding.SourceCharge.tally (AccountAction.phaseCharge downstreamTechnology downstreamGraph) material +
      ((material.frontier.map sourceRead).map (programCharge downstreamTechnology downstreamGraph)).sum := by
  rw [SourceAccountedAction.occurrenceUpdate, RootedAccountedUnfolding.SourceCharge.advance, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro current _
  exact (programCharge_source downstreamTechnology downstreamGraph current).symm

end
end FiniteADCWholeJointCurrent.Information.Packet.Recovered
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
