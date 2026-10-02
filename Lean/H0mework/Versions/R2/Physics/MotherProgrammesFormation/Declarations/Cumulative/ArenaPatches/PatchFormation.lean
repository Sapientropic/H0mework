import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Patches
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.PatchFormation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- Missing build requests remain missing. Every supplied original patch is
recovered with its actual finite rows, selectors and generated remainder. -/
theorem every_patch_request_section (parent : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms parent = some value) (desired : OriginalPatchRequests value) :
    ∃ material : M, ∃ inventories : FiniteSection value.2.2.2.2,
      ∃ selections : ∀ context, LedgerTransportedRemainderCoverageAt (inventories context),
        formPatchRequests material = some ⟨⟨⟨value, inventories⟩, selections⟩, desired⟩ := by
  let inventories := fun context => RequestEncoding.inventory value.2.2.2.2 context (desired context)
  let selections := fun context => RequestEncoding.selections value.2.2.2.2 context (desired context)
  obtain ⟨inventoryMaterial, inventoryFormed⟩ := every_finite_inventory parent value formed inventories
  obtain ⟨selectionMaterial, selectionFormed⟩ :=
    every_selection_section inventoryMaterial ⟨value, inventories⟩ inventoryFormed selections
  let selected : SelectionValue := ⟨⟨value, inventories⟩, selections⟩
  let inventoryParent := ((MotherArenaHigher.split rank) selectionMaterial).1
  let programmeParent := ((MotherArenaHigher.split rank) inventoryParent).1
  let inventoryOrigin := selections_inventory_formed selectionMaterial selected selectionFormed
  let programmeOrigin := inventory_programmes_formed inventoryParent selected.1 inventoryOrigin
  let coordinates := sourceCoordinates programmeParent value programmeOrigin
  let ledger := ledgerCoordinates programmeParent value programmeOrigin
  let reader : B → ℕ → ℝ := fun code _ => Function.extend (MotherArenaExact.remainderContextEmbedding coordinates ledger)
    (fun context => (RequestEncoding.kind value.2.2.2.2 context (desired context) : ℝ)) (fun _ => 0) code
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) reader
  refine ⟨(MotherArenaHigher.pack rank) (selectionMaterial, material), inventories, selections, ?_⟩
  unfold formPatchRequests
  rw [MotherArenaHigher.split_pack]
  dsimp only
  unfold formPatchRequestParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨selected, selectionFormed, ?_⟩
  have values : patchRequests selectionMaterial material selected selectionFormed = desired := by
    funext context
    change patchOfKind? value.2.2.2.2 context (inventories context) (selections context)
      (Nat.floor ((MotherArenaHigher.read rank) material (MotherArenaExact.remainderContextEmbedding coordinates ledger context) 0)) = desired context
    rw [hm]
    dsimp only [reader]
    rw [(MotherArenaExact.remainderContextEmbedding coordinates ledger).injective.extend_apply, Nat.floor_natCast]
    exact RequestEncoding.recovered value.2.2.2.2 context (desired context)
  exact congrArg (fun requests => some (⟨selected, requests⟩ : Σ value : SelectionValue, PatchRequests value)) values

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
