import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalFactory
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalCoverage

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

namespace TerminalBodyEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source)
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (rowCode : ∀ context, RowEvents rows context ↪ MotherArenaHigher.Base rank)
    (desired : TerminalBodies rows)

def lengthReader : B → ℝ :=
  Function.extend (coordinates.occurrence) (fun context => ((desired context).1 : ℝ)) (fun _ => 0)

def graph (code : B) (tag : Nat) : Prop :=
  let pair := (MotherArenaHigher.unpair rank) code
  ∃ (context : Point source), ∃ index : Fin (desired context).1,
    coordinates.occurrence context = pair.1 ∧ 1 + index.val = tag ∧
      terminalItemAddress rows ledger rowCode context ((desired context).2 index) = pair.2

def reader (code : B) (tag : Nat) : ℝ :=
  if tag = 0 then lengthReader rows coordinates desired code
  else if graph rows coordinates ledger rowCode desired code tag then 0 else 1

theorem size_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger rowCode desired)
    (context : Point source) : terminalSize coordinates material context = (desired context).1 := by
  unfold terminalSize
  rw [hm]
  simp only [reader, lengthReader]
  rw [(coordinates.occurrence).injective.extend_apply]
  exact Nat.floor_natCast _

theorem cell_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger rowCode desired)
    (context : Point source) (index : Fin (terminalSize coordinates material context)) (item : TerminalItem rows context) :
    r2 material (1 + index.val) (coordinates.occurrence context) (terminalItemAddress rows ledger rowCode context item) ↔
      item = (desired context).2 (Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index) := by
  have nonzero : ¬ (1 + index.val = 0) := by omega
  rw [r2, bit, hm]
  simp only [reader, nonzero, if_false]
  have selected : (if graph rows coordinates ledger rowCode desired
      ((MotherArenaHigher.pair rank) (coordinates.occurrence context, terminalItemAddress rows ledger rowCode context item))
      (1 + index.val) then (0 : ℝ) else 1) = 0 ↔
      graph rows coordinates ledger rowCode desired
        ((MotherArenaHigher.pair rank) (coordinates.occurrence context, terminalItemAddress rows ledger rowCode context item))
        (1 + index.val) := by
    split <;> simp_all only [one_ne_zero, iff_self]
  rw [selected]
  simp only [graph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, chosen, contextEq, indexEq, itemEq⟩
    have same := (coordinates.occurrence).injective contextEq
    cases same
    have same : chosen = Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index :=
      Fin.ext (Nat.add_left_cancel indexEq)
    cases same
    exact ((terminalItemAddress rows ledger rowCode context).injective itemEq).symm
  · intro same
    cases same
    exact ⟨context, Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index, rfl, rfl, rfl⟩

theorem checked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger rowCode desired)
     : TerminalBodyCheck rows coordinates ledger rowCode material := by
  intro context index
  exact ⟨(desired context).2 (Fin.cast (size_eq rows coordinates ledger rowCode desired hm context) index),
    (cell_graph rows coordinates ledger rowCode desired hm context index _).mpr rfl,
    fun item selected => (cell_graph rows coordinates ledger rowCode desired hm context index item).mp selected⟩

private theorem cast_section {A : Type} {left right : Nat} (same : left = right) (values : Fin right → A) :
    HEq (fun index : Fin left => values (Fin.cast same index)) values := by
  cases same
  rfl

theorem body_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader rows coordinates ledger rowCode desired)
    (context : Point source) :
    generatedTerminalBodies rows coordinates ledger rowCode material (checked rows coordinates ledger rowCode desired hm) context = desired context := by
  change (⟨terminalSize coordinates material context,
    fun index => Classical.choose (checked rows coordinates ledger rowCode desired hm context index)⟩ : TerminalBody rows context) =
      ⟨(desired context).1, (desired context).2⟩
  have sizeEq := size_eq rows coordinates ledger rowCode desired hm context
  have values : (fun index => Classical.choose (checked rows coordinates ledger rowCode desired hm context index)) =
      fun index => (desired context).2 (Fin.cast sizeEq index) := by
    funext index
    exact (cell_graph rows coordinates ledger rowCode desired hm context index _).mp
      (Classical.choose_spec (checked rows coordinates ledger rowCode desired hm context index)).1
  apply Sigma.ext sizeEq
  exact (heq_of_eq values).trans (cast_section sizeEq ((desired context).2))

end TerminalBodyEncoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
