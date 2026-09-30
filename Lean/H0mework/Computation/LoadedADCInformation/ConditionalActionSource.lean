import H0mework.Realization.OccurrenceCharge.Model
import H0mework.Computation.LoadedADCInformation.Consumer

/-! Complete command words are read from the old material frontier; the real feedback action generates their update. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.ConditionalAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory

def driveFlip (drive : FiniteBinaryDrive) : FiniteBinaryDrive :=
  fun channel => !(drive channel)

def driveRead (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) : Carrier FiniteBinaryDrive :=
  sourcePoint current.plant.val.drive

def materialRead (material : RootedAccountedUnfolding (FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) : Carrier FiniteBinaryDrive :=
  observation driveRead (SourceAccountedAction.frontierWord material)

def commandAction : Carrier FiniteBinaryDrive →ₗ[ℤ] Carrier FiniteBinaryDrive := sourceAction driveFlip

theorem command_action_injective : Function.Injective commandAction := by
  apply Finsupp.mapDomain_injective
  intro left right same
  funext channel
  have equality := congrFun same channel
  have twice := congrArg Bool.not equality
  simpa only [driveFlip, Bool.not_not] using twice

theorem drive_source_square :
    (observation (driveRead (hardware := hardware) (actualBoot := actualBoot) (technology := technology))).comp
      (sourceAction (loadedStep downstreamTechnology downstreamGraph)) =
    commandAction.comp (observation driveRead) := by
  apply Finsupp.lhom_ext'
  intro current
  apply LinearMap.ext_ring
  change observation driveRead (sourceAction (loadedStep downstreamTechnology downstreamGraph) (sourcePoint current)) =
    commandAction (observation driveRead (sourcePoint current))
  rw [sourceAction_point, observation_point, observation_point]
  change sourcePoint (loadedStep downstreamTechnology downstreamGraph current).plant.val.drive =
    sourceAction driveFlip (sourcePoint current.plant.val.drive)
  rw [sourceAction_point, loadedStep_feedback]
  rfl

theorem material_source_square (material : RootedAccountedUnfolding (FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) :
    materialRead (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph) material) =
      commandAction (materialRead material) := by
  change observation driveRead (SourceAccountedAction.frontierWord
    (material.advance (fun current => .zero (loadedStep downstreamTechnology downstreamGraph current)))) = _
  rw [← SourceAccountedAction.frontier_action]
  exact LinearMap.congr_fun (drive_source_square downstreamTechnology downstreamGraph) _

theorem material_read_history (bound : Nat) :
    materialRead (loadedExposure downstreamTechnology downstreamGraph seed bound) =
      sourcePoint (driveAt downstreamTechnology downstreamGraph seed bound) := by
  simp [materialRead, SourceAccountedAction.frontierWord, loadedExposure_frontier, driveRead, driveAt]

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
