import H0mework.Fock.HistoryCopy.InformationProjection
import H0mework.Fock.HistoryCopy.ObservationInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceConditionalInventory SourceUniformFibreVariance SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance growthParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem joint_old_material (depth bound : Nat) (index : Index depth) :
    joint (depth + 1) bound (FamilyModel.Fock.oldIndex depth index) = joint depth bound index := by
  funext actor
  apply Prod.ext
  · exact (before_source (depth + 1) bound actor).trans (before_source depth bound actor).symm
  · exact (after_source (depth + 1) bound (FamilyModel.Fock.oldIndex depth index) actor).trans
      (after_source depth bound index actor).symm

theorem inventory_append (depth bound : Nat) (index : Index depth) :
    cost (bound + 1) (joint depth (bound + 1) index) = cost bound (joint depth bound index) +
      if joint depth (bound + 1) index (Fin.last (bound + 1)) ∈ outputs bound (joint depth bound index) then 1 else 0 := by
  have generated := SourceCopyInventory.original_cost_step depth bound index
  have same : (fun actor : Fin (bound + 1) => SourceCopyInventory.read (NativeCopy.Fock.material depth index) actor.val) =
      joint depth bound index := (funext (SourceCopyInventory.joint_source depth bound index)).symm
  have fresh : SourceCopyInventory.read (NativeCopy.Fock.material depth index) (bound + 1) =
      joint depth (bound + 1) index (Fin.last (bound + 1)) :=
    (SourceCopyInventory.joint_source depth (bound + 1) index (Fin.last (bound + 1))).symm
  unfold SourceCopyInventory.increment at generated
  rw [fresh, same] at generated
  exact generated

theorem dynamic_cost_step (depth : Nat) (index : Index depth) :
    cost (depth + 1) (joint (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)) =
      cost depth (joint depth depth index) +
        if joint depth (depth + 1) index (Fin.last (depth + 1)) ∈ outputs depth (joint depth depth index) then 1 else 0 := by
  rw [joint_old_material]
  exact inventory_append depth depth index

theorem written_joint (depth : Nat) (index : Index depth) :
    joint depth (depth + 1) index (Fin.last (depth + 1)) =
      (sourceStateAt (runtimePayload depth).nativeWrite.target,
        sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth index) (runtimePayload depth).nativeWrite.target)) := by
  exact (SourceCopyInventory.joint_source depth (depth + 1) index (Fin.last (depth + 1))).trans
    (SourceCopyInventory.written_read (NativeCopy.Fock.material depth index) depth)

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
