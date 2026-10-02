import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.SelectionFactory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

def completeOfPartial? {context : RemainderContext source}
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩)
    (selected : LedgerTransportedRemainderCoverageAt inventory) : Option (LedgerCompleteFiniteCoverageAt inventory) :=
  if total : (∀ entry, (selected.destinationIndex entry).isSome = true) ∧
      (∀ entry, (selected.originIndex entry).isSome = true) then
    some {
      destinationIndex := fun entry => ((selected.destinationIndex entry).get (total.1 entry)).val
      originIndex := fun entry => ((selected.originIndex entry).get (total.2 entry)).val
      destination_sound := fun entry => ((selected.destinationIndex entry).get (total.1 entry)).property
      origin_sound := fun entry => ((selected.originIndex entry).get (total.2 entry)).property }
  else none

def identityPatch (context : RemainderContext source) (same : context.1.2.1 = context.2)
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩)
    (selected : LedgerTransportedRemainderCoverageAt inventory) :
    FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩ := by
  rcases context with ⟨point, target⟩
  change point.2.1 = target at same
  subst target
  exact .identityRemainder inventory {
    destinationIndex := selected.destinationIndex
    originIndex := selected.originIndex }

/-- Branch material selects an original constructor. A transported remainder
is supplied only by the original generator at this exact occurrence/target. -/
def patchOfKind? (context : RemainderContext source)
    (inventory : FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩)
    (selected : LedgerTransportedRemainderCoverageAt inventory) :
    Nat → Option (FiniteGeneratedLedgerWritePatchAt rows context.1.2 ⟨context.2⟩)
  | 0 => if same : context.1.2.1 = context.2 then some (identityPatch rows context same inventory selected) else none
  | 1 => (completeOfPartial? rows inventory selected).map (fun coverage => .complete inventory coverage)
  | 2 => (rows.generateTransportedRemainder? context.1.2 ⟨context.2⟩).map
      (fun remainder => .transportedRemainder inventory selected remainder)
  | _ => none

abbrev SelectionValue := Σ value : InventoryValue, SelectionSection value

theorem selections_inventory_formed (material : M) (value : SelectionValue)
    (formed : formSelections material = some value) :
    formInventories (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold formSelections formSelectionParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact baseFormed.trans (congrArg some (congrArg Sigma.fst (Option.some.inj selected)))
  · cases selected

abbrev PatchRequests (value : SelectionValue) :=
  (context : RemainderContext value.1.1.1.2.2) →
    Option (FiniteGeneratedLedgerWritePatchAt value.1.1.2.2.2.2 context.1.2 ⟨context.2⟩)

def patchRequests (parent material : M) (value : SelectionValue) (formed : formSelections parent = some value) :
    PatchRequests value :=
  let inventoryParent := (MotherHigherLawValue.split parent).1
  let programmeParent := (MotherHigherLawValue.split inventoryParent).1
  let inventoryFormed := selections_inventory_formed parent value formed
  let programmeFormed := inventory_programmes_formed inventoryParent value.1 inventoryFormed
  let coordinates := sourceCoordinates programmeParent value.1.1 programmeFormed
  let ledger := ledgerCoordinates programmeParent value.1.1 programmeFormed
  fun context => patchOfKind? value.1.1.2.2.2.2 context (value.1.2 context) (value.2 context)
    (Nat.floor (MotherHigherLawFormation.read material (remainderContextEmbedding coordinates ledger context) 0))

def formPatchRequestParts (parent material : M) : Option (Σ value : SelectionValue, PatchRequests value) :=
  (formSelections parent).pbind (fun value formed => some ⟨value, patchRequests parent material value formed⟩)

/-- A build-time parser over the already formed programmes, inventories and
selectors. Final compiler formation consumes success at its actual targets. -/
def formPatchRequests (material : M) : Option (Σ value : SelectionValue, PatchRequests value) :=
  let parts := MotherHigherLawValue.split material
  formPatchRequestParts parts.1 parts.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
