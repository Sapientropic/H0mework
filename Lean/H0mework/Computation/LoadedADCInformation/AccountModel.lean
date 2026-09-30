import H0mework.Computation.LoadedADCInformation.AccountSource

/-! The already generated Model reads and advances the same complete ADC account. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.AccountAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory SourceGeneratedActionObservationHistory

abbrev CurrentModel :=
  Model (sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
    (observation (SourceAccountedAction.retained (phaseCharge (hardware := hardware)
      (actualBoot := actualBoot) (technology := technology) downstreamTechnology downstreamGraph)))

def modelAt (bound : Nat) : CurrentModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph :=
  projection (sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
    (observation (SourceAccountedAction.retained (phaseCharge downstreamTechnology downstreamGraph)))
    (sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed bound))

def readModel : CurrentModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph →ₗ[ℤ]
      Carrier (FiniteADCWholeJointCurrent hardware
        (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) × (ℝ × ℝ × ℝ) :=
  modelReadout _ _

def advanceModel : CurrentModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph →ₗ[ℤ] CurrentModel (hardware := hardware) (actualBoot := actualBoot)
      (technology := technology) downstreamTechnology downstreamGraph :=
  modelAction _ _

theorem read_model (bound : Nat) :
    readModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed bound) =
      stateRead downstreamTechnology downstreamGraph seed bound := by
  change modelReadout _ _ (projection _ _ (sourcePoint _)) = _
  rw [modelReadout_projection, observation_point, stateRead_is_retained]

theorem next_model (bound : Nat) :
    advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed bound) =
      modelAt downstreamTechnology downstreamGraph seed (bound + 1) := by
  exact SourceAccountedAction.model_next (loadedStep downstreamTechnology downstreamGraph)
    (phaseCharge downstreamTechnology downstreamGraph) (loadedExposure downstreamTechnology downstreamGraph seed bound)

theorem next_model_is_calculation (bound : Nat) :
    readModel downstreamTechnology downstreamGraph
      (advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed bound)) =
      SourceAccountedAction.update (loadedStep downstreamTechnology downstreamGraph)
        (phaseCharge downstreamTechnology downstreamGraph)
        (readModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed bound)) := by
  rw [next_model, read_model, read_model, incremental_next]

theorem forecast_whole_account (bound : Nat) :
    let predicted := SourceAccountedAction.update (loadedStep downstreamTechnology downstreamGraph)
      (phaseCharge downstreamTechnology downstreamGraph) (stateRead downstreamTechnology downstreamGraph seed bound)
    (jointStoredEnergy (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed bound))).value -
        (jointStoredEnergy seed).value = predicted.2.2.1 - predicted.2.2.2 := by
  dsimp only
  rw [incremental_next, ← loadedAfter_succ]
  exact whole_material_account downstreamTechnology downstreamGraph seed (bound + 1)

end
end FiniteADCWholeJointCurrent.Information.AccountAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
