import H0mework.Versions.X.Fock.HistoryCopy.InformationSource
import H0mework.Versions.X.Fock.HistoryCopy.ObservationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyInventory

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceCopyObservation
open SourceConditionalInventory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance projectionParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem joint_source (depth bound : Nat) (index : SourceCopyObservation.Index depth) (actor : Fin (bound + 1)) :
    SourceCopyObservation.joint depth bound index actor = read (NativeCopy.Fock.material depth index) actor.val := by
  apply Prod.ext
  · exact before_source depth bound actor
  · exact (congrArg (copySnapshot depth index) (Actor.originalRead_actual depth bound actor)).trans
      (copy_snapshot_point depth index ((runtimeAt actor.val).current.visit.current : Current))

theorem cost_is_original (depth bound : Nat) (index : SourceCopyObservation.Index depth) :
    inventoryCost (NativeCopy.Fock.material depth index) bound =
      SourceConditionalInventory.cost bound (SourceCopyObservation.joint depth bound index) := by
  exact congrArg (SourceConditionalInventory.cost bound) (funext (joint_source depth bound index)).symm

theorem original_cost_step (depth bound : Nat) (index : SourceCopyObservation.Index depth) :
    SourceConditionalInventory.cost (bound + 1) (SourceCopyObservation.joint depth (bound + 1) index) =
      SourceConditionalInventory.cost bound (SourceCopyObservation.joint depth bound index) +
        increment (NativeCopy.Fock.material depth index) bound := by
  rw [← cost_is_original, ← cost_is_original]
  exact cost_step (NativeCopy.Fock.material depth index) bound

end
end SourceCopyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
