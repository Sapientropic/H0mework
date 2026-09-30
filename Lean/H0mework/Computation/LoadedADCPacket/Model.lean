import H0mework.Computation.LoadedADCPacket.Conditional

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOwnedObservationHistory SourceGeneratedActionObservationHistory
noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def currentRead (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    Carrier (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  sourcePoint current.packet

def materialRead (material : RootedAccountedUnfolding (FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) :
    Carrier (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  observation currentRead (SourceAccountedAction.frontierWord material)

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

abbrev PacketModel :=
  Model (sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
    (observation (materialRead (hardware := hardware) (actualBoot := actualBoot) (technology := technology)))

def modelAt (frame : Nat) : PacketModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph :=
  projection (sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
    (observation materialRead) (sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed frame))

def readModel : PacketModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph →ₗ[ℤ]
      Carrier (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  modelReadout _ _

def advanceModel : PacketModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph →ₗ[ℤ] PacketModel (hardware := hardware) (actualBoot := actualBoot)
      (technology := technology) downstreamTechnology downstreamGraph :=
  modelAction _ _

theorem material_read_history (frame : Nat) :
    materialRead (loadedExposure downstreamTechnology downstreamGraph seed frame) =
      sourcePoint (loadedAfter downstreamTechnology downstreamGraph seed frame).packet := by
  simp [materialRead, SourceAccountedAction.frontierWord, loadedExposure_frontier, currentRead]
  rfl

theorem read_model (frame : Nat) :
    readModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed frame) =
      sourcePoint (loadedAfter downstreamTechnology downstreamGraph seed frame).packet := by
  rw [modelAt, readModel, modelReadout_projection, observation_point, material_read_history]

theorem next_model (frame : Nat) :
    advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed frame) =
      modelAt downstreamTechnology downstreamGraph seed (frame + 1) := by
  rw [advanceModel, modelAt, modelAction_source, sourceAction_point]
  rfl

theorem read_model_next (bound : Nat) (actor : Fin (bound + 1)) :
    readModel downstreamTechnology downstreamGraph
      (advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed actor.val)) =
      sourcePoint (nextPacket downstreamTechnology downstreamGraph seed bound actor) := by
  rw [next_model, read_model, next_is_original_history]
  rfl

private theorem action_power_history (frame future : Nat) :
    ((sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))) ^ future)
      (sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed frame)) =
        sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed (frame + future)) := by
  induction future with
  | zero => simp
  | succ future previous =>
      rw [pow_succ', Module.End.mul_apply, previous, sourceAction_point]
      change sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed (frame + future + 1)) =
        sourcePoint (loadedExposure downstreamTechnology downstreamGraph seed (frame + (future + 1)))
      rw [Nat.add_assoc]

theorem model_history_fibre (left right : Nat) :
    modelAt downstreamTechnology downstreamGraph seed left = modelAt downstreamTechnology downstreamGraph seed right ↔
      ∀ future : Nat,
        (loadedAfter downstreamTechnology downstreamGraph seed (left + future)).packet =
          (loadedAfter downstreamTechnology downstreamGraph seed (right + future)).packet := by
  rw [modelAt, modelAt, model_fibre_iff]
  simp only [action_power_history, observation_point, material_read_history]
  have injective : Function.Injective
      (sourcePoint : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → Carrier Code) :=
    Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0)
  constructor
  · intro same future
    apply injective
    exact same future
  · intro same future
    exact congrArg sourcePoint (same future)

theorem conditional_model_next (bound : Nat)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((SourceGeneratedRuntimeHistoryProbability.historyPMF bound).map
      (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    (SourceConditionalHistory.conditional (SourceGeneratedRuntimeHistoryProbability.historyPMF bound)
      (nowPacket downstreamTechnology downstreamGraph seed bound) value supported).map
      (fun actor => readModel downstreamTechnology downstreamGraph
        (advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed actor.val))) =
    (conditionalNext downstreamTechnology downstreamGraph seed bound value supported).map sourcePoint := by
  rw [conditionalNext, SourceConditionalNext.conditionalNext, PMF.map_comp]
  congr 1
  funext actor
  exact read_model_next downstreamTechnology downstreamGraph seed bound actor

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
