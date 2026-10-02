import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteEncoding
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.RemainderEncoding

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact.WriteEncoding
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ MotherArenaHigher.Base rank)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding (rank := rank) rows)

def remainderGraph (tag : Nat) (code : B) : Prop :=
  let head := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) head.2
  match tag with
  | 0 => ∃ context event, remainderContextEmbedding coordinates ledger context = head.1 ∧ encode.remainder ⟨context, event⟩ = head.2
  | 1 => ∃ context event, remainderContextEmbedding coordinates ledger context = head.1 ∧ encode.remainder ⟨context, event⟩ = head.2 ∧
      rows.transportedRemainderSource.emit? context.1.2 context.2 = some event
  | 2 => ∃ (event : Sigma (RemainderEvents rows)), ∃ entry,
      remainderInputEmbedding coordinates ledger operations rows encode event = head.1 ∧
      ledger.entry event.1.1.2.1 entry = tail.1 ∧
      exactCode (destinationContext event.1 (rows.transportedRemainderSource.compileEvolution event.2) entry)
        ((rows.transportedRemainderSource.compileExact event.2).destination entry) = tail.2
  | 3 => ∃ (event : Sigma (RemainderEvents rows)), ∃ entry,
      remainderInputEmbedding coordinates ledger operations rows encode event = head.1 ∧
      ledger.entry event.1.2 entry = tail.1 ∧
      exactCode (originContext event.1 (rows.transportedRemainderSource.compileEvolution event.2) entry)
        ((rows.transportedRemainderSource.compileExact event.2).origin entry) = tail.2
  | _ => False

def remainderReader (code : B) (tag : Nat) : ℝ := if remainderGraph coordinates ledger operations exactCode rows encode tag code then 0 else 1

theorem remainderReader_bit {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (tag : Nat) (code : B) : bit material tag code ↔ remainderGraph coordinates ledger operations exactCode rows encode tag code := by
  by_cases seen : remainderGraph coordinates ledger operations exactCode rows encode tag code <;>
    simp only [bit, hm, remainderReader, seen, if_true, if_false, one_ne_zero, iff_self]

def remainderEquiv {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (context : RemainderContext source) : RemainderEvents rows context ≃ RemainderEvent coordinates ledger material context :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk context).trans encode.remainder)
    (fun address => r2 material 0 (remainderContextEmbedding coordinates ledger context) address) (by
      intro address
      rw [r2, remainderReader_bit coordinates ledger operations exactCode rows encode hm]
      simp only [remainderGraph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, event, same, valueEq⟩
        have same := (remainderContextEmbedding coordinates ledger).injective same
        cases same
        exact ⟨event, valueEq⟩
      · rintro ⟨event, valueEq⟩
        exact ⟨context, event, rfl, valueEq⟩)

theorem selected_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (context : RemainderContext source) (event : RemainderEvents rows context) :
    r2 material 1 (remainderContextEmbedding coordinates ledger context)
      (remainderEquiv coordinates ledger operations exactCode rows encode hm context event).val ↔
        rows.transportedRemainderSource.emit? context.1.2 context.2 = some event := by
  rw [r2, remainderReader_bit coordinates ledger operations exactCode rows encode hm]
  simp only [remainderGraph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, value, contextEq, eventEq, selected⟩
    have same := (remainderContextEmbedding coordinates ledger).injective contextEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := RemainderEvents rows) context).trans encode.remainder).injective eventEq
    cases same
    exact selected
  · intro selected
    exact ⟨context, event, rfl, rfl, selected⟩

theorem destination_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (context : RemainderContext source) (event : RemainderEvents rows context) (entry : OpenResponsibilityAt N context.1.2.1)
    (output : operations.Exact (destinationContext context (rows.transportedRemainderSource.compileEvolution event) entry)) :
    r3 material 2 (remainderInputEmbedding coordinates ledger operations rows encode ⟨context, event⟩)
      (ledger.entry context.1.2.1 entry) (exactCode _ output) ↔
        output = (rows.transportedRemainderSource.compileExact event).destination entry := by
  rw [r3, remainderReader_bit coordinates ledger operations exactCode rows encode hm]
  simp only [remainderGraph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, otherEntry, contextEq, entryEq, valueEq⟩
    have same := (remainderInputEmbedding coordinates ledger operations rows encode).injective contextEq
    cases same
    have same := (ledger.entry context.1.2.1).injective entryEq
    cases same
    exact ((exactCode _).injective valueEq).symm
  · intro same
    cases same
    exact ⟨⟨context, event⟩, entry, rfl, rfl, rfl⟩

theorem origin_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (context : RemainderContext source) (event : RemainderEvents rows context) (entry : OpenResponsibilityAt N context.2)
    (output : operations.Exact (originContext context (rows.transportedRemainderSource.compileEvolution event) entry)) :
    r3 material 3 (remainderInputEmbedding coordinates ledger operations rows encode ⟨context, event⟩)
      (ledger.entry context.2 entry) (exactCode _ output) ↔
        output = (rows.transportedRemainderSource.compileExact event).origin entry := by
  rw [r3, remainderReader_bit coordinates ledger operations exactCode rows encode hm]
  simp only [remainderGraph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, otherEntry, contextEq, entryEq, valueEq⟩
    have same := (remainderInputEmbedding coordinates ledger operations rows encode).injective contextEq
    cases same
    have same := (ledger.entry context.2).injective entryEq
    cases same
    exact ((exactCode _).injective valueEq).symm
  · intro same
    cases same
    exact ⟨⟨context, event⟩, entry, rfl, rfl, rfl⟩

theorem tableChecked {material wholeMaterial : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode)
    (context : RemainderContext source) (event : RemainderEvent coordinates ledger material context) :
    MotherArenaCompiler.WriteCheck ledger wholeMaterial (remainderEventKey coordinates ledger context event.val) context.1.2.1 context.2 := by
  obtain ⟨event, rfl⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective event
  exact wholeChecked coordinates ledger operations rows encode hw ⟨context, event⟩

theorem table_eq {material wholeMaterial : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode)
    (context : RemainderContext source) (event : RemainderEvents rows context) :
    MotherArenaCompiler.write ledger wholeMaterial (remainderEventKey coordinates ledger context
      (remainderEquiv coordinates ledger operations exactCode rows encode hm context event).val) _ _
      (tableChecked coordinates ledger operations exactCode rows encode hm hw context
        (remainderEquiv coordinates ledger operations exactCode rows encode hm context event)) =
          rows.transportedRemainderSource.compileEvolution event :=
  whole_eq coordinates ledger operations rows encode hw ⟨context, event⟩

theorem remainderChecked {material wholeMaterial : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode) :
    RemainderCheck coordinates ledger operations exactCode material wholeMaterial where
  tables := tableChecked coordinates ledger operations exactCode rows encode hm hw
  destination := by
    intro context event entry
    obtain ⟨event, rfl⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective event
    dsimp only
    rw [table_eq coordinates ledger operations exactCode rows encode hm hw context event]
    exact ⟨(rows.transportedRemainderSource.compileExact event).destination entry,
      (destination_graph coordinates ledger operations exactCode rows encode hm context event entry _).mpr rfl,
      fun output selected => (destination_graph coordinates ledger operations exactCode rows encode hm context event entry output).mp selected⟩
  origin := by
    intro context event entry
    obtain ⟨event, rfl⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective event
    dsimp only
    rw [table_eq coordinates ledger operations exactCode rows encode hm hw context event]
    exact ⟨(rows.transportedRemainderSource.compileExact event).origin entry,
      (origin_graph coordinates ledger operations exactCode rows encode hm context event entry _).mpr rfl,
      fun output selected => (origin_graph coordinates ledger operations exactCode rows encode hm context event entry output).mp selected⟩
  selected_unique := by
    intro context left right hl hr
    obtain ⟨left, rfl⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective left
    obtain ⟨right, rfl⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective right
    exact congrArg (remainderEquiv coordinates ledger operations exactCode rows encode hm context)
      (Option.some.inj (((selected_graph coordinates ledger operations exactCode rows encode hm context left).mp hl).symm.trans
        ((selected_graph coordinates ledger operations exactCode rows encode hm context right).mp hr)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact.WriteEncoding
