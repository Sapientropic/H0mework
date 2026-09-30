import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.SelectionFactory
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Patches

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

theorem selections_inventory_formed (material : M) (value : SelectionValue)
    (formed : formSelections material = some value) :
    formInventories ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold formSelections formSelectionParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact baseFormed.trans (congrArg some (congrArg Sigma.fst (Option.some.inj selected)))
  · cases selected

def patchRequests (parent material : M) (value : SelectionValue) (formed : formSelections parent = some value) :
    PatchRequests value :=
  let inventoryParent := ((MotherArenaHigher.split rank) parent).1
  let programmeParent := ((MotherArenaHigher.split rank) inventoryParent).1
  let inventoryFormed := selections_inventory_formed parent value formed
  let programmeFormed := inventory_programmes_formed inventoryParent value.1 inventoryFormed
  let coordinates := sourceCoordinates programmeParent value.1.1 programmeFormed
  let ledger := ledgerCoordinates programmeParent value.1.1 programmeFormed
  fun context => patchOfKind? value.1.1.2.2.2.2 context (value.1.2 context) (value.2 context)
    (Nat.floor ((MotherArenaHigher.read rank) material (MotherArenaExact.remainderContextEmbedding coordinates ledger context) 0))

def formPatchRequestParts (parent material : M) : Option (Σ value : SelectionValue, PatchRequests value) :=
  (formSelections parent).pbind (fun value formed => some ⟨value, patchRequests parent material value formed⟩)

/-- A build-time parser over the already formed programmes, inventories and
selectors. Final compiler formation consumes success at its actual targets. -/
def formPatchRequests (material : M) : Option (Σ value : SelectionValue, PatchRequests value) :=
  let parts := (MotherArenaHigher.split rank) material
  formPatchRequestParts parts.1 parts.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
