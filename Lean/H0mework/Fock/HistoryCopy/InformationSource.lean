import H0mework.Fock.HistoryCopy.Action
import H0mework.Probability.Information.InventoryGrowth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyInventory

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalInventory SourceUniformFibreVariance
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance sourceParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def read (material : Current) (state : Nat) : ParentCarrier × ParentCarrier :=
  (sourceStateAt (runtimeAt state).current.visit.current,
    sourceStateAt (NativeCopy.copy material (runtimeAt state).current.visit.current))

def inventoryCost (material : Current) (bound : Nat) : ℝ :=
  cost bound (fun actor => read material actor.val)

def increment (material : Current) (bound : Nat) : ℝ :=
  if read material (bound + 1) ∈ outputs bound (fun actor => read material actor.val) then 1 else 0

theorem cost_step (material : Current) (bound : Nat) :
    inventoryCost material (bound + 1) = inventoryCost material bound + increment material bound :=
  cost_append bound (read material)

theorem written_read (material : Current) (depth : Nat) :
    read material (depth + 1) =
      (sourceStateAt (runtimePayload depth).nativeWrite.target,
        sourceStateAt (NativeCopy.copy material (runtimePayload depth).nativeWrite.target)) := by
  have next : ((runtimeAt (depth + 1)).current.visit.current : Current) = (runtimePayload depth).nativeWrite.target :=
    runtime_current_next depth
  exact congrArg (fun current => (sourceStateAt current, sourceStateAt (NativeCopy.copy material current))) next

end
end SourceCopyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
