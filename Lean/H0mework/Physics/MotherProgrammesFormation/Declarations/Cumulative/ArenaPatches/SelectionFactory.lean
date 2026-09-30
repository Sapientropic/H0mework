import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.SelectionCoverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.SelectionFactory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem inventory_programmes_formed (material : M) (value : InventoryValue)
    (formed : formInventories material = some value) :
    MotherArenaExact.formWritePrograms ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold formInventories formInventoryParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact baseFormed.trans (congrArg some (congrArg Sigma.fst (Option.some.inj selected)))
  · cases selected

def formSelectionParts (parent material : M) : Option (Σ value : InventoryValue, SelectionSection value) :=
  (formInventories parent).pbind (fun value formed =>
    let base := ((MotherArenaHigher.split rank) parent).1
    let programmes := inventory_programmes_formed parent value formed
    let coordinates := sourceCoordinates base value.1 programmes
    let ledger := ledgerCoordinates base value.1 programmes
    if checked : SelectionCheck value.1.2.2.2.2 coordinates ledger value.2 material then
      some ⟨value, transportedCoverage value.1.2.2.2.2 coordinates ledger value.2 material checked⟩
    else none)

def formSelections (material : M) : Option (Σ value : InventoryValue, SelectionSection value) :=
  let parts := (MotherArenaHigher.split rank) material
  formSelectionParts parts.1 parts.2

theorem every_selection_section (parent : M) (value : InventoryValue) (formed : formInventories parent = some value)
    (desired : SelectionSection value) : ∃ material : M, formSelections material = some ⟨value, desired⟩ := by
  let base := ((MotherArenaHigher.split rank) parent).1
  let programmes := inventory_programmes_formed parent value formed
  let coordinates := sourceCoordinates base value.1 programmes
  let ledger := ledgerCoordinates base value.1 programmes
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (SelectionEncoding.reader value.1.2.2.2.2 coordinates ledger value.2 desired)
  refine ⟨(MotherArenaHigher.pack rank) (parent, material), ?_⟩
  unfold formSelections
  rw [MotherArenaHigher.split_pack]
  dsimp only
  unfold formSelectionParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨value, formed, ?_⟩
  let checked := SelectionEncoding.checked value.1.2.2.2.2 coordinates ledger value.2 desired hm
  rw [dif_pos checked]
  exact congrArg (fun selection => some (⟨value, selection⟩ : Σ value : InventoryValue, SelectionSection value))
    (funext (SelectionEncoding.coverage_eq value.1.2.2.2.2 coordinates ledger value.2 desired hm))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
