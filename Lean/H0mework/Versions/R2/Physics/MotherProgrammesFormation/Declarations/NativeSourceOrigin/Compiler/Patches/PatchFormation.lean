import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.PatchRecovery

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

namespace RequestEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

def inventory (context : RemainderContext source)
    (request : Option (FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩)) :
    FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩ :=
  match request with
  | none => {
      size := 0
      sourceEntryAt := Fin.elim0
      targetEntryAt := Fin.elim0
      rowAt := fun index => index.elim0 }
  | some patch => patchInventory rows patch

def selections (context : RemainderContext source)
    (request : Option (FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩)) :
    LedgerTransportedRemainderCoverageAt (inventory rows context request) := by
  cases request with
  | none => exact { destinationIndex := fun _ => none, originIndex := fun _ => none }
  | some patch => exact patchSelections rows patch

def kind (context : RemainderContext source)
    (request : Option (FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩)) : Nat :=
  match request with
  | none => 3
  | some patch => patchKind rows patch

theorem recovered (context : RemainderContext source)
    (request : Option (FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩)) :
    patchOfKind? rows context (inventory rows context request) (selections rows context request) (kind rows context request) = request := by
  cases request with
  | none => rfl
  | some patch => exact patch_recovered rows patch

end RequestEncoding

abbrev OriginalPatchRequests (value : WriteProgramValue) :=
  (context : RemainderContext value.1.2.2) →
    Option (FiniteGeneratedLedgerWritePatchAt value.2.2.2.2 context.1.2 ⟨context.2⟩)

/-- Missing build requests remain missing. Every supplied original patch is
recovered with its actual finite rows, selectors and generated remainder. -/
theorem every_patch_request_section (parent : M) (value : WriteProgramValue)
    (formed : formWritePrograms parent = some value) (desired : OriginalPatchRequests value) :
    ∃ material : M, ∃ inventories : FiniteSection value.2.2.2.2,
      ∃ selections : ∀ context, LedgerTransportedRemainderCoverageAt (inventories context),
        formPatchRequests material = some ⟨⟨⟨value, inventories⟩, selections⟩, desired⟩ := by
  let inventories := fun context => RequestEncoding.inventory value.2.2.2.2 context (desired context)
  let selections := fun context => RequestEncoding.selections value.2.2.2.2 context (desired context)
  obtain ⟨inventoryMaterial, inventoryFormed⟩ := every_finite_inventory parent value formed inventories
  obtain ⟨selectionMaterial, selectionFormed⟩ :=
    every_selection_section inventoryMaterial ⟨value, inventories⟩ inventoryFormed selections
  let selected : SelectionValue := ⟨⟨value, inventories⟩, selections⟩
  let inventoryParent := (MotherHigherLawValue.split selectionMaterial).1
  let programmeParent := (MotherHigherLawValue.split inventoryParent).1
  let inventoryOrigin := selections_inventory_formed selectionMaterial selected selectionFormed
  let programmeOrigin := inventory_programmes_formed inventoryParent selected.1 inventoryOrigin
  let coordinates := sourceCoordinates programmeParent value programmeOrigin
  let ledger := ledgerCoordinates programmeParent value programmeOrigin
  let reader : B → ℕ → ℝ := fun code _ => Function.extend (remainderContextEmbedding coordinates ledger)
    (fun context => (RequestEncoding.kind value.2.2.2.2 context (desired context) : ℝ)) (fun _ => 0) code
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective reader
  refine ⟨MotherHigherLawValue.pack (selectionMaterial, material), inventories, selections, ?_⟩
  unfold formPatchRequests
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  unfold formPatchRequestParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨selected, selectionFormed, ?_⟩
  have values : patchRequests selectionMaterial material selected selectionFormed = desired := by
    funext context
    change patchOfKind? value.2.2.2.2 context (inventories context) (selections context)
      (Nat.floor (MotherHigherLawFormation.read material (remainderContextEmbedding coordinates ledger context) 0)) = desired context
    rw [hm]
    dsimp only [reader]
    rw [(remainderContextEmbedding coordinates ledger).injective.extend_apply, Nat.floor_natCast]
    exact RequestEncoding.recovered value.2.2.2.2 context (desired context)
  exact congrArg (fun requests => some (⟨selected, requests⟩ : Σ value : SelectionValue, PatchRequests value)) values

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
