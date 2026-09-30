import H0mework.Versions.X.Fock.ReceivedStep.ActionCoordinate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

theorem coordinate_transport {left right stride : Nat} (same : left = right)
    (data : (Fin ((left + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) (position : Nat) :
    coordinateAt right stride
      (cast (congrArg (fun bound => (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) same) data) position =
      coordinateAt left stride data position := by
  cases same
  rfl

theorem moments_transport {left right stride : Nat} (same : left = right)
    (data : (Fin ((left + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    (cast (congrArg (fun bound => (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) same) data).2 = data.2 := by
  cases same
  rfl

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def nextData (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
    (previous : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    (Fin ((inventoryBound runtime.tick.next + 1) * ((maximumIndex runtime.tick.next).val + 1)) → ℚ) × ℚ × ℚ :=
  cast (congrArg (fun bound => (Fin ((bound + 1) * ((maximumIndex runtime.tick.next).val + 1)) → ℚ) × ℚ × ℚ)
    (SourceActualImageStep.next_bound runtime).symm)
    (advanceData (inventoryBound runtime) index.val (maximumIndex runtime.tick.next).val count selected previous)

theorem next_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
    (previous : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) (position : Nat) :
    coordinateAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
      (nextData runtime index count selected previous) position =
      if selected then coordinateAt (inventoryBound runtime) index.val previous position + ((count + 1 : Nat) : ℚ)⁻¹ *
        ((if position = inventoryBound runtime + 2 then 1 else 0) - coordinateAt (inventoryBound runtime) index.val previous position)
      else coordinateAt (inventoryBound runtime) index.val previous position := by
  rw [nextData, coordinate_transport (SourceActualImageStep.next_bound runtime).symm]
  exact advance_coordinate _ _ _ _ _ _ (capacity_grows runtime index) (birth_included runtime) position

theorem next_moments (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
    (previous : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    (nextData runtime index count selected previous).2 =
      if selected then
        (previous.2.1 + ((count + 1 : Nat) : ℚ)⁻¹ * (1 - previous.2.1),
          previous.2.2 + ((count + 1 : Nat) : ℚ)⁻¹ * ((inventoryBound runtime + 3 : ℚ) - previous.2.2))
      else previous.2 := by
  rw [nextData, moments_transport (SourceActualImageStep.next_bound runtime).symm]
  cases selected <;> rfl

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
