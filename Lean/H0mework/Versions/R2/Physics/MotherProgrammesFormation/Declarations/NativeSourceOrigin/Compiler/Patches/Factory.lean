import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

abbrev RowItem (context : RemainderContext source) :=
  Σ a : OpenResponsibilityAt N context.1.2.1, Σ b : OpenResponsibilityAt N context.2,
    rows.IncidenceOccurrenceAt context.1.2 a b

def itemAddress (ledger : LedgerCoordinates N) (rowCode : ∀ context, WriteEvents rows context ↪ B)
    (context : RemainderContext source) : RowItem rows context ↪ B where
  toFun := fun ⟨a, b, event⟩ => MotherHigherLawFamily.pair (ledger.entry context.1.2.1 a,
    MotherHigherLawFamily.pair (ledger.entry context.2 b, rowCode ⟨context.1.1, context.1.2, context.2, a, b⟩ event))
  inj' := by
    rintro ⟨a, b, event⟩ ⟨a', b', event'⟩ same
    have headEq := MotherHigherLawFamily.pair_injective same
    have same := (ledger.entry context.1.2.1).injective (congrArg Prod.fst headEq)
    cases same
    have tailEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd headEq)
    have same := (ledger.entry context.2).injective (congrArg Prod.fst tailEq)
    cases same
    have same := (rowCode ⟨context.1.1, context.1.2, context.2, a, b⟩).injective (congrArg Prod.snd tailEq)
    cases same
    rfl

variable (coordinates : Coordinates source) (ledger : LedgerCoordinates N)
    (rowCode : ∀ context, WriteEvents rows context ↪ B)

def sizeAt (material : M) (context : RemainderContext source) : Nat :=
  Nat.floor (MotherHigherLawFormation.read material (remainderContextEmbedding coordinates ledger context) 0)

def FiniteCheck (material : M) (context : RemainderContext source) : Prop :=
  ∀ index : Fin (sizeAt coordinates ledger material context), ∃! item : RowItem rows context,
    r2 material (1 + index.val) (remainderContextEmbedding coordinates ledger context) (itemAddress rows ledger rowCode context item)

/-- The original generator seals every stored source event. Fin indices
retain the complete ordering and repeated entries/events. -/
def inventory (material : M) (context : RemainderContext source)
    (checked : FiniteCheck rows coordinates ledger rowCode material context) :
    FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩ where
  size := sizeAt coordinates ledger material context
  sourceEntryAt := fun index => (Classical.choose (checked index)).1
  targetEntryAt := fun index => (Classical.choose (checked index)).2.1
  rowAt := fun index => rows.generate (Classical.choose (checked index)).2.2

abbrev FiniteSection := (context : RemainderContext source) → FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩

def formInventoryParts (parent material : M) : Option (Σ value : WriteProgramValue, FiniteSection value.2.2.2.2) :=
  (formWritePrograms parent).pbind (fun value formed =>
    let coordinates := sourceCoordinates parent value formed
    let ledger := ledgerCoordinates parent value formed
    let rowCode := rowAddresses parent value formed
    if checked : ∀ context, FiniteCheck value.2.2.2.2 coordinates ledger rowCode material context then
      some ⟨value, fun context => inventory value.2.2.2.2 coordinates ledger rowCode material context (checked context)⟩
    else none)

def formInventories (material : M) : Option (Σ value : WriteProgramValue, FiniteSection value.2.2.2.2) :=
  let parts := MotherHigherLawValue.split material
  formInventoryParts parts.1 parts.2

theorem inventories_formed (parent material : M) (value : WriteProgramValue)
    (formed : formWritePrograms parent = some value)
    (checked : ∀ context, FiniteCheck value.2.2.2.2 (sourceCoordinates parent value formed)
      (ledgerCoordinates parent value formed) (rowAddresses parent value formed) material context) :
    formInventories (MotherHigherLawValue.pack (parent, material)) =
      some ⟨value, fun context => inventory value.2.2.2.2 (sourceCoordinates parent value formed)
        (ledgerCoordinates parent value formed) (rowAddresses parent value formed) material context (checked context)⟩ := by
  unfold formInventories
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  unfold formInventoryParts
  apply Option.pbind_eq_some_iff.mpr
  exact ⟨value, formed, dif_pos checked⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
