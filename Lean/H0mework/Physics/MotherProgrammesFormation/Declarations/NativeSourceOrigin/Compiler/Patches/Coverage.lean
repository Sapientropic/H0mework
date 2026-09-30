import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Body

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

namespace InventoryEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (coordinates : Coordinates source) (ledger : LedgerCoordinates N) (rowCode : ∀ context, WriteEvents rows context ↪ B)
    (desired : FiniteSection rows)

def itemAt (context : RemainderContext source) (index : Fin (desired context).size) : RowItem rows context :=
  ⟨(desired context).sourceEntryAt index, (desired context).targetEntryAt index, ((desired context).rowAt index).event⟩

def lengthReader : B → ℝ :=
  Function.extend (remainderContextEmbedding coordinates ledger) (fun context => ((desired context).size : ℝ)) (fun _ => 0)

def graph (code : B) (tag : Nat) : Prop :=
  let pair := MotherHigherLawFamily.unpair code
  ∃ (context : RemainderContext source), ∃ index : Fin (desired context).size,
    remainderContextEmbedding coordinates ledger context = pair.1 ∧ 1 + index.val = tag ∧
      itemAddress rows ledger rowCode context (itemAt rows desired context index) = pair.2

def reader (code : B) (tag : Nat) : ℝ :=
  if tag = 0 then lengthReader rows coordinates ledger desired code
  else if graph rows coordinates ledger rowCode desired code tag then 0 else 1

theorem size_eq {material : M}
    (hm : MotherHigherLawFormation.read material = reader rows coordinates ledger rowCode desired)
    (context : RemainderContext source) : sizeAt coordinates ledger material context = (desired context).size := by
  unfold sizeAt
  rw [hm]
  simp only [reader, lengthReader]
  rw [(remainderContextEmbedding coordinates ledger).injective.extend_apply]
  exact Nat.floor_natCast _

theorem cell_graph {material : M}
    (hm : MotherHigherLawFormation.read material = reader rows coordinates ledger rowCode desired)
    (context : RemainderContext source) (index : Fin (sizeAt coordinates ledger material context)) (item : RowItem rows context) :
    r2 material (1 + index.val) (remainderContextEmbedding coordinates ledger context) (itemAddress rows ledger rowCode context item) ↔
      item = itemAt rows desired context (Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index) := by
  have nonzero : ¬ (1 + index.val = 0) := by omega
  rw [r2, bit, hm]
  simp only [reader, nonzero, if_false]
  have selected : (if graph rows coordinates ledger rowCode desired
      (MotherHigherLawFamily.pair (remainderContextEmbedding coordinates ledger context, itemAddress rows ledger rowCode context item))
      (1 + index.val) then (0 : ℝ) else 1) = 0 ↔
      graph rows coordinates ledger rowCode desired
        (MotherHigherLawFamily.pair (remainderContextEmbedding coordinates ledger context, itemAddress rows ledger rowCode context item))
        (1 + index.val) := by
    split <;> simp_all only [one_ne_zero, iff_self]
  rw [selected]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, chosen, contextEq, indexEq, itemEq⟩
    have same := (remainderContextEmbedding coordinates ledger).injective contextEq
    cases same
    have same : chosen = Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index :=
      Fin.ext (Nat.add_left_cancel indexEq)
    cases same
    exact ((itemAddress rows ledger rowCode context).injective itemEq).symm
  · intro same
    cases same
    exact ⟨context, Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index, rfl, rfl, rfl⟩

theorem checked {material : M}
    (hm : MotherHigherLawFormation.read material = reader rows coordinates ledger rowCode desired)
    (context : RemainderContext source) : FiniteCheck rows coordinates ledger rowCode material context := by
  intro index
  exact ⟨itemAt rows desired context (Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index),
    (cell_graph rows coordinates ledger rowCode desired hm context index _).mpr rfl,
    fun item selected => (cell_graph rows coordinates ledger rowCode desired hm context index item).mp selected⟩

private theorem cast_section {A : Type} {left right : Nat} (same : left = right) (values : Fin right → A) :
    HEq (fun index : Fin left => values (Fin.cast same index)) values := by
  cases same
  rfl

theorem inventory_eq {material : M}
    (hm : MotherHigherLawFormation.read material = reader rows coordinates ledger rowCode desired)
    (context : RemainderContext source) :
    inventory rows coordinates ledger rowCode material context (checked rows coordinates ledger rowCode desired hm context) = desired context := by
  apply (inventoryBodyEquiv rows context).injective
  change (⟨sizeAt coordinates ledger material context,
    fun index => Classical.choose (checked rows coordinates ledger rowCode desired hm context index)⟩ : InventoryBody rows context) =
      ⟨(desired context).size, itemAt rows desired context⟩
  have sizeEq := size_eq rows coordinates ledger rowCode desired hm context
  have values : (fun index => Classical.choose (checked rows coordinates ledger rowCode desired hm context index)) =
      fun index => itemAt rows desired context (Fin.cast sizeEq index) := by
    funext index
    exact (cell_graph rows coordinates ledger rowCode desired hm context index _).mp
      (Classical.choose_spec (checked rows coordinates ledger rowCode desired hm context index)).1
  apply Sigma.ext sizeEq
  exact (heq_of_eq values).trans (cast_section sizeEq (itemAt rows desired context))

end InventoryEncoding

theorem every_finite_inventory (parent : M) (value : WriteProgramValue) (formed : formWritePrograms parent = some value)
    (desired : FiniteSection value.2.2.2.2) :
    ∃ material : M, formInventories material = some ⟨value, desired⟩ := by
  let coordinates := sourceCoordinates parent value formed
  let ledger := ledgerCoordinates parent value formed
  let rowCode := rowAddresses parent value formed
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective
    (InventoryEncoding.reader value.2.2.2.2 coordinates ledger rowCode desired)
  refine ⟨MotherHigherLawValue.pack (parent, material), ?_⟩
  have generated := inventories_formed parent material value formed
    (InventoryEncoding.checked value.2.2.2.2 coordinates ledger rowCode desired hm)
  have inventories : (fun context => inventory value.2.2.2.2 coordinates ledger rowCode material context
      (InventoryEncoding.checked value.2.2.2.2 coordinates ledger rowCode desired hm context)) = desired :=
    funext (InventoryEncoding.inventory_eq value.2.2.2.2 coordinates ledger rowCode desired hm)
  exact generated.trans (congrArg (fun rows => some (⟨value, rows⟩ : Σ value : WriteProgramValue, FiniteSection value.2.2.2.2)) inventories)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
