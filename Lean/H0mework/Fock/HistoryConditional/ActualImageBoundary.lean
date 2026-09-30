import H0mework.Fock.HistoryConditional.ActualImageProbability

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def first (runtime : LivingRuntimeState process) : Image runtime.tick.next :=
  SourceConditionalNext.Image.actual (nextRead runtime.tick.next) 0

def birth (runtime : LivingRuntimeState process) : Image runtime.tick.next :=
  SourceConditionalNext.Image.actual (nextRead runtime.tick.next) (Fin.last (inventoryBound runtime.tick.next))

theorem step_ne_first (runtime : LivingRuntimeState process) (value : Image runtime) : step runtime value ≠ first runtime := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
  rw [actual, step_actual]
  intro equality
  have indices := nextRead_injective runtime.tick.next (congrArg Subtype.val equality)
  have positions := congrArg Fin.val indices
  change index.val + 1 = 0 at positions
  omega

theorem retain_ne_birth (runtime : LivingRuntimeState process) (value : Image runtime) : retain runtime value ≠ birth runtime := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
  rw [actual, retain_actual]
  intro equality
  have indices := nextRead_injective runtime.tick.next (congrArg Subtype.val equality)
  have positions := congrArg Fin.val indices
  change index.val = inventoryBound runtime.tick.next at positions
  have prior := index.isLt
  have next := next_bound runtime
  omega

theorem step_complete (runtime : LivingRuntimeState process) (target : Image runtime.tick.next) :
    (∃ source : Image runtime, step runtime source = target) ∨ target = first runtime := by
  obtain ⟨index, same⟩ := target.property
  have actual : target = SourceConditionalNext.Image.actual (nextRead runtime.tick.next) index := Subtype.ext same.symm
  by_cases zero : index.val = 0
  · right
    rw [actual]
    exact congrArg (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) (Fin.ext zero)
  · left
    have limit := index.isLt
    have next := next_bound runtime
    let old : Actors runtime := ⟨index.val - 1, by omega⟩
    refine ⟨SourceConditionalNext.Image.actual (nextRead runtime) old, ?_⟩
    rw [step_actual, actual]
    apply congrArg (SourceConditionalNext.Image.actual (nextRead runtime.tick.next))
    apply Fin.ext
    change index.val - 1 + 1 = index.val
    omega

theorem retain_complete (runtime : LivingRuntimeState process) (target : Image runtime.tick.next) :
    (∃ source : Image runtime, retain runtime source = target) ∨ target = birth runtime := by
  obtain ⟨index, same⟩ := target.property
  have actual : target = SourceConditionalNext.Image.actual (nextRead runtime.tick.next) index := Subtype.ext same.symm
  by_cases old : index.val < inventoryBound runtime + 1
  · left
    refine ⟨SourceConditionalNext.Image.actual (nextRead runtime) ⟨index.val, old⟩, ?_⟩
    rw [retain_actual, actual]
    exact congrArg (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) (Fin.ext rfl)
  · right
    rw [actual]
    apply congrArg (SourceConditionalNext.Image.actual (nextRead runtime.tick.next))
    apply Fin.ext
    have limit := index.isLt
    have next := next_bound runtime
    change index.val = inventoryBound runtime.tick.next
    omega

theorem birth_read (runtime : LivingRuntimeState process) :
    read runtime.tick.next (birth runtime) = SourceConditionalInventory.born (inventoryBound runtime) := by
  rw [birth, read_actual, next_bound]
  rfl

theorem first_read (runtime : LivingRuntimeState process) :
    read runtime.tick.next (first runtime) = SourceCopyNativeModelStep.sourceValue (runtimeAt 1) := by
  rw [first, read_actual]
  rfl

theorem step_fibre (runtime : LivingRuntimeState process) (target : Image runtime.tick.next) :
    (∃! source, step runtime source = target) ↔ target ≠ first runtime := by
  constructor
  · rintro ⟨source, same, _⟩ equal
    exact step_ne_first runtime source (same.trans equal)
  · intro different
    obtain ⟨source, same⟩ := (step_complete runtime target).resolve_right different
    exact ⟨source, same, fun candidate equal => step_injective runtime (equal.trans same.symm)⟩

theorem retain_fibre (runtime : LivingRuntimeState process) (target : Image runtime.tick.next) :
    (∃! source, retain runtime source = target) ↔ target ≠ birth runtime := by
  constructor
  · rintro ⟨source, same, _⟩ equal
    exact retain_ne_birth runtime source (same.trans equal)
  · intro different
    obtain ⟨source, same⟩ := (retain_complete runtime target).resolve_right different
    exact ⟨source, same, fun candidate equal => retain_injective runtime (equal.trans same.symm)⟩

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
