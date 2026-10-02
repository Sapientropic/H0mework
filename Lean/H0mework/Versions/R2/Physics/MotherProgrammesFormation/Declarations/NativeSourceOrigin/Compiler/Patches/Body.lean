import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

abbrev InventoryBody (context : RemainderContext source) := Σ size : Nat, Fin size → RowItem rows context

def inventoryBodyEquiv (context : RemainderContext source) :
    FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩ ≃ InventoryBody rows context where
  toFun := fun value => ⟨value.size, fun index => ⟨value.sourceEntryAt index, value.targetEntryAt index, (value.rowAt index).event⟩⟩
  invFun := fun value => {
    size := value.1
    sourceEntryAt := fun index => (value.2 index).1
    targetEntryAt := fun index => (value.2 index).2.1
    rowAt := fun index => rows.generate (value.2 index).2.2 }
  left_inv := by
    rintro ⟨size, sourceEntryAt, targetEntryAt, rowAt⟩
    dsimp only
    congr 1
    funext index
    exact (writeSealEquiv rows ⟨context.1.1, context.1.2, context.2, sourceEntryAt index, targetEntryAt index⟩).symm_apply_apply (rowAt index)
  right_inv := fun _ => rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
