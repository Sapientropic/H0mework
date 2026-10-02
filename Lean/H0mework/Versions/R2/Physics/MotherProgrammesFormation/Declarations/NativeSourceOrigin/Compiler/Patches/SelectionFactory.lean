import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.SelectionCoverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev InventoryValue := Σ value : WriteProgramValue, FiniteSection value.2.2.2.2

theorem inventory_programmes_formed (material : M) (value : InventoryValue)
    (formed : formInventories material = some value) :
    formWritePrograms (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold formInventories formInventoryParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact baseFormed.trans (congrArg some (congrArg Sigma.fst (Option.some.inj selected)))
  · cases selected

abbrev SelectionSection (value : InventoryValue) :=
  ∀ context, LedgerTransportedRemainderCoverageAt (value.2 context)

def formSelectionParts (parent material : M) : Option (Σ value : InventoryValue, SelectionSection value) :=
  (formInventories parent).pbind (fun value formed =>
    let base := (MotherHigherLawValue.split parent).1
    let programmes := inventory_programmes_formed parent value formed
    let coordinates := sourceCoordinates base value.1 programmes
    let ledger := ledgerCoordinates base value.1 programmes
    if checked : SelectionCheck value.1.2.2.2.2 coordinates ledger value.2 material then
      some ⟨value, transportedCoverage value.1.2.2.2.2 coordinates ledger value.2 material checked⟩
    else none)

def formSelections (material : M) : Option (Σ value : InventoryValue, SelectionSection value) :=
  let parts := MotherHigherLawValue.split material
  formSelectionParts parts.1 parts.2

theorem every_selection_section (parent : M) (value : InventoryValue) (formed : formInventories parent = some value)
    (desired : SelectionSection value) : ∃ material : M, formSelections material = some ⟨value, desired⟩ := by
  let base := (MotherHigherLawValue.split parent).1
  let programmes := inventory_programmes_formed parent value formed
  let coordinates := sourceCoordinates base value.1 programmes
  let ledger := ledgerCoordinates base value.1 programmes
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective
    (SelectionEncoding.reader value.1.2.2.2.2 coordinates ledger value.2 desired)
  refine ⟨MotherHigherLawValue.pack (parent, material), ?_⟩
  unfold formSelections
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  unfold formSelectionParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨value, formed, ?_⟩
  let checked := SelectionEncoding.checked value.1.2.2.2.2 coordinates ledger value.2 desired hm
  rw [dif_pos checked]
  exact congrArg (fun selection => some (⟨value, selection⟩ : Σ value : InventoryValue, SelectionSection value))
    (funext (SelectionEncoding.coverage_eq value.1.2.2.2.2 coordinates ledger value.2 desired hm))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
