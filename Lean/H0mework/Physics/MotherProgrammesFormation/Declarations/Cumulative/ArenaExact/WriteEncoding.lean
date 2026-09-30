import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteFactory
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteEncoding

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure WriteEncoding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) where
  row : Sigma (WriteEvents rows) ↪ B
  remainder : Sigma (RemainderEvents rows) ↪ B

namespace WriteEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ MotherArenaHigher.Base rank)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding (rank := rank) rows)

def rowGraph (tag : Nat) (code : B) : Prop :=
  let head := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) head.2
  if tag = 0 then
    ∃ context event, writeContextEmbedding coordinates ledger context = head.1 ∧ encode.row ⟨context, event⟩ = head.2
  else
    ∃ context event, writeContextEmbedding coordinates ledger context = head.1 ∧ encode.row ⟨context, event⟩ = tail.1 ∧
      1 + (MotherArenaCompiler.rowKey ledger (rows.compileEvolution event)).1 = tag ∧
      (MotherArenaHigher.pair rank) ((MotherArenaCompiler.rowKey ledger (rows.compileEvolution event)).2,
        exactCode context (rows.compileExact event)) = tail.2

def rowReader (code : B) (tag : Nat) : ℝ := if rowGraph coordinates ledger operations exactCode rows encode tag code then 0 else 1

theorem rowReader_bit {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = rowReader coordinates ledger operations exactCode rows encode)
    (tag : Nat) (code : B) : bit material tag code ↔ rowGraph coordinates ledger operations exactCode rows encode tag code := by
  by_cases seen : rowGraph coordinates ledger operations exactCode rows encode tag code <;>
    simp only [bit, hm, rowReader, seen, if_true, if_false, one_ne_zero, iff_self]

def rowEquiv {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = rowReader coordinates ledger operations exactCode rows encode)
    (context : WriteContext source) : WriteEvents rows context ≃ WriteEvent coordinates ledger material context :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk context).trans encode.row)
    (fun address => r2 material 0 (writeContextEmbedding coordinates ledger context) address) (by
      intro address
      rw [r2, rowReader_bit coordinates ledger operations exactCode rows encode hm]
      simp only [rowGraph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, event, same, valueEq⟩
        have same := (writeContextEmbedding coordinates ledger).injective same
        cases same
        exact ⟨event, valueEq⟩
      · rintro ⟨event, valueEq⟩
        exact ⟨context, event, rfl, valueEq⟩)

theorem row_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = rowReader coordinates ledger operations exactCode rows encode)
    (context : WriteContext source) (event : WriteEvents rows context) (output : RowOutput operations context) :
    rowOutputGraph coordinates ledger operations exactCode material context
      (rowEquiv coordinates ledger operations exactCode rows encode hm context event).val output ↔
        output = (rows.compileEvolution event, rows.compileExact event) := by
  rw [rowOutputGraph, r3, rowReader_bit coordinates ledger operations exactCode rows encode hm]
  simp only [rowGraph, MotherArenaHigher.unpair_pair, show ¬ (1 + (MotherArenaCompiler.rowKey ledger output.1).1 = 0) by omega, if_false]
  constructor
  · rintro ⟨other, value, contextEq, eventEq, tagEq, outputEq⟩
    have same := (writeContextEmbedding coordinates ledger).injective contextEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := WriteEvents rows) context).trans encode.row).injective eventEq
    cases same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective outputEq
    exact Prod.ext (MotherArenaCompiler.rowKey_injective ledger (Prod.ext (Nat.add_left_cancel tagEq) (congrArg Prod.fst pairEq))).symm
      ((exactCode context).injective (congrArg Prod.snd pairEq)).symm
  · intro same
    cases same
    exact ⟨context, event, rfl, rfl, rfl, rfl⟩

theorem rowChecked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = rowReader coordinates ledger operations exactCode rows encode) :
    WriteRowCheck coordinates ledger operations exactCode material := by
  intro context event
  obtain ⟨event, rfl⟩ := (rowEquiv coordinates ledger operations exactCode rows encode hm context).surjective event
  exact ⟨(rows.compileEvolution event, rows.compileExact event),
    (row_graph coordinates ledger operations exactCode rows encode hm context event _).mpr rfl,
    fun output selected => (row_graph coordinates ledger operations exactCode rows encode hm context event output).mp selected⟩

def remainderInputEmbedding : Sigma (RemainderEvents rows) ↪ B where
  toFun := fun event => remainderEventKey coordinates ledger event.1 (encode.remainder event)
  inj' := by
    intro left right same
    exact encode.remainder.injective (congrArg Prod.snd ((MotherArenaHigher.pairEquiv rank).injective same))

def wholeGraph (code : B) (tag : Nat) : Prop :=
  let head := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) head.2
  ∃ event : Sigma (RemainderEvents rows), remainderInputEmbedding coordinates ledger operations rows encode event = head.1 ∧
    MotherArenaCompiler.writePage ledger (rows.transportedRemainderSource.compileEvolution event.2) tag tail.1 tail.2

def wholeReader (code : B) (tag : Nat) : ℝ := if wholeGraph coordinates ledger operations rows encode code tag then 0 else 1

theorem wholeReader_bit {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = wholeReader coordinates ledger operations rows encode)
    (code : B) (tag : Nat) : bit material tag code ↔ wholeGraph coordinates ledger operations rows encode code tag := by
  by_cases seen : wholeGraph coordinates ledger operations rows encode code tag <;>
    simp only [bit, hm, wholeReader, seen, if_true, if_false, one_ne_zero, iff_self]

theorem whole_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = wholeReader coordinates ledger operations rows encode)
    (event : Sigma (RemainderEvents rows)) (tag : Nat) (input output : B) :
    r3 material tag (remainderInputEmbedding coordinates ledger operations rows encode event) input output ↔
      MotherArenaCompiler.writePage ledger (rows.transportedRemainderSource.compileEvolution event.2) tag input output := by
  rw [r3, wholeReader_bit coordinates ledger operations rows encode hm]
  simp only [wholeGraph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, same, selected⟩
    have same := (remainderInputEmbedding coordinates ledger operations rows encode).injective same
    cases same
    exact selected
  · intro selected
    exact ⟨event, rfl, selected⟩

theorem wholeChecked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = wholeReader coordinates ledger operations rows encode)
    (event : Sigma (RemainderEvents rows)) :
    MotherArenaCompiler.WriteCheck ledger material (remainderInputEmbedding coordinates ledger operations rows encode event) event.1.1.2.1 event.1.2 :=
  MotherArenaCompiler.writeCheckOfPage ledger (rows.transportedRemainderSource.compileEvolution event.2)
    (whole_graph coordinates ledger operations rows encode hm event)

theorem whole_eq {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = wholeReader coordinates ledger operations rows encode)
    (event : Sigma (RemainderEvents rows)) :
    MotherArenaCompiler.write ledger material (remainderInputEmbedding coordinates ledger operations rows encode event) _ _
      (wholeChecked coordinates ledger operations rows encode hm event) = rows.transportedRemainderSource.compileEvolution event.2 :=
  MotherArenaCompiler.write_eq_of_page ledger (rows.transportedRemainderSource.compileEvolution event.2)
    (whole_graph coordinates ledger operations rows encode hm event)

end WriteEncoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
