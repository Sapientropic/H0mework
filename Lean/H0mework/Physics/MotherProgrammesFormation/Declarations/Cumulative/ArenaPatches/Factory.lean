import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Coordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Factory

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

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)

def itemAddress (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (rowCode : ∀ context, WriteEvents rows context ↪ B)
    (context : RemainderContext source) : RowItem rows context ↪ B where
  toFun := fun ⟨a, b, event⟩ => (MotherArenaHigher.pair rank) (ledger.entry context.1.2.1 a,
    (MotherArenaHigher.pair rank) (ledger.entry context.2 b, rowCode ⟨context.1.1, context.1.2, context.2, a, b⟩ event))
  inj' := by
    rintro ⟨a, b, event⟩ ⟨a', b', event'⟩ same
    have headEq := (MotherArenaHigher.pairEquiv rank).injective same
    have same := (ledger.entry context.1.2.1).injective (congrArg Prod.fst headEq)
    cases same
    have tailEq := (MotherArenaHigher.pairEquiv rank).injective (congrArg Prod.snd headEq)
    have same := (ledger.entry context.2).injective (congrArg Prod.fst tailEq)
    cases same
    have same := (rowCode ⟨context.1.1, context.1.2, context.2, a, b⟩).injective (congrArg Prod.snd tailEq)
    cases same
    rfl

variable (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N)
    (rowCode : ∀ context, WriteEvents rows context ↪ MotherArenaHigher.Base rank)

def sizeAt (material : M) (context : RemainderContext source) : Nat :=
  Nat.floor ((MotherArenaHigher.read rank) material (MotherArenaExact.remainderContextEmbedding coordinates ledger context) 0)

def FiniteCheck (material : M) (context : RemainderContext source) : Prop :=
  ∀ index : Fin (sizeAt coordinates ledger material context), ∃! item : RowItem rows context,
    r2 material (1 + index.val) (MotherArenaExact.remainderContextEmbedding coordinates ledger context) (itemAddress rows ledger rowCode context item)

/-- The original generator seals every stored source event. Fin indices
retain the complete ordering and repeated entries/events. -/
def inventory (material : M) (context : RemainderContext source)
    (checked : FiniteCheck rows coordinates ledger rowCode material context) :
    FiniteGeneratedLedgerWriteRowsAt rows context.1.2 ⟨context.2⟩ where
  size := sizeAt coordinates ledger material context
  sourceEntryAt := fun index => (Classical.choose (checked index)).1
  targetEntryAt := fun index => (Classical.choose (checked index)).2.1
  rowAt := fun index => rows.generate (Classical.choose (checked index)).2.2

def formInventoryParts (parent material : M) : Option (Σ value : WriteProgramValue, FiniteSection value.2.2.2.2) :=
  (MotherArenaExact.formWritePrograms parent).pbind (fun value formed =>
    let coordinates := sourceCoordinates parent value formed
    let ledger := ledgerCoordinates parent value formed
    let rowCode := rowAddresses parent value formed
    if checked : ∀ context, FiniteCheck value.2.2.2.2 coordinates ledger rowCode material context then
      some ⟨value, fun context => inventory value.2.2.2.2 coordinates ledger rowCode material context (checked context)⟩
    else none)

def formInventories (material : M) : Option (Σ value : WriteProgramValue, FiniteSection value.2.2.2.2) :=
  let parts := (MotherArenaHigher.split rank) material
  formInventoryParts parts.1 parts.2

theorem inventories_formed (parent material : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms parent = some value)
    (checked : ∀ context, FiniteCheck value.2.2.2.2 (sourceCoordinates parent value formed)
      (ledgerCoordinates parent value formed) (rowAddresses parent value formed) material context) :
    formInventories ((MotherArenaHigher.pack rank) (parent, material)) =
      some ⟨value, fun context => inventory value.2.2.2.2 (sourceCoordinates parent value formed)
        (ledgerCoordinates parent value formed) (rowAddresses parent value formed) material context (checked context)⟩ := by
  unfold formInventories
  rw [MotherArenaHigher.split_pack]
  dsimp only
  unfold formInventoryParts
  apply Option.pbind_eq_some_iff.mpr
  exact ⟨value, formed, dif_pos checked⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
