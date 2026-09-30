import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.RemainderEncoding
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteReadback

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact.WriteEncoding
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
open MotherExactPrograms.WriteEncoding (castMember Certification castCertification
  castCertification_destination castCertification_origin certification_ext)
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ MotherArenaHigher.Base rank)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding (rank := rank) rows)

theorem remainder_emit {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = remainderReader coordinates ledger operations exactCode rows encode)
    (context : RemainderContext source) :
    Option.map (remainderEquiv coordinates ledger operations exactCode rows encode hm context)
      (rows.transportedRemainderSource.emit? context.1.2 context.2) = remainderSelected? coordinates ledger material context := by
  unfold remainderSelected?
  split
  · rename_i selected
    obtain ⟨event, eventEq⟩ := (remainderEquiv coordinates ledger operations exactCode rows encode hm context).surjective (Classical.choose selected)
    have emitted := (selected_graph coordinates ledger operations exactCode rows encode hm context event).mp (by
      rw [eventEq]
      exact Classical.choose_spec selected)
    rw [emitted]
    exact congrArg some eventEq
  · rename_i absent
    cases emitted : rows.transportedRemainderSource.emit? context.1.2 context.2 with
    | none => rfl
    | some event =>
        exact False.elim (absent ⟨_, (selected_graph coordinates ledger operations exactCode rows encode hm context event).mpr emitted⟩)

def writeValue {rowMaterial remainderMaterial wholeMaterial : MotherArenaHigher.Material rank}
    (hr : (MotherArenaHigher.read rank) rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : (MotherArenaHigher.read rank) remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode) :
    LedgerWriteRowSourceAt source operations.exactTransitionAt :=
  generatedWriteSource coordinates ledger operations exactCode rowMaterial remainderMaterial wholeMaterial
    (rowChecked coordinates ledger operations exactCode rows encode hr)
    (remainderChecked coordinates ledger operations exactCode rows encode hm hw)

section
variable {rowMaterial remainderMaterial wholeMaterial : MotherArenaHigher.Material rank}
    (hr : (MotherArenaHigher.read rank) rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : (MotherArenaHigher.read rank) remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode)

theorem row_value (context : WriteContext source) (event : WriteEvents rows context) :
    let generated := writeValue coordinates ledger operations exactCode rows encode hr hm hw
    let value := rowEquiv coordinates ledger operations exactCode rows encode hr context event
    (generated.compileEvolution value, generated.compileExact value) = (rows.compileEvolution event, rows.compileExact event) :=
  (row_graph coordinates ledger operations exactCode rows encode hr context event _).mp
    (Classical.choose_spec (rowChecked coordinates ledger operations exactCode rows encode hr context
      (rowEquiv coordinates ledger operations exactCode rows encode hr context event))).1

theorem whole_value (context : RemainderContext source) (event : RemainderEvents rows context) :
    (writeValue coordinates ledger operations exactCode rows encode hr hm hw).transportedRemainderSource.compileEvolution
      (remainderEquiv coordinates ledger operations exactCode rows encode hm context event) =
        rows.transportedRemainderSource.compileEvolution event :=
  table_eq coordinates ledger operations exactCode rows encode hm hw context event

end

theorem castMember_code {left right : WriteContext source} (same : left = right) (value : operations.Exact left) :
    exactCode right (castMember operations same value) = exactCode left value := by
  cases same
  rfl

theorem certification_value {rowMaterial remainderMaterial wholeMaterial : MotherArenaHigher.Material rank}
    (hr : (MotherArenaHigher.read rank) rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : (MotherArenaHigher.read rank) remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = wholeReader coordinates ledger operations rows encode)
    (context : RemainderContext source) (event : RemainderEvents rows context) :
    castCertification operations context (whole_value coordinates ledger operations exactCode rows encode hr hm hw context event)
      ((writeValue coordinates ledger operations exactCode rows encode hr hm hw).transportedRemainderSource.compileExact
        (remainderEquiv coordinates ledger operations exactCode rows encode hm context event)) =
          rows.transportedRemainderSource.compileExact event := by
  let result := writeValue coordinates ledger operations exactCode rows encode hr hm hw
  let value := remainderEquiv coordinates ledger operations exactCode rows encode hm context event
  let same := whole_value coordinates ledger operations exactCode rows encode hr hm hw context event
  apply certification_ext operations context
  · funext entry
    refine (castCertification_destination operations context same (result.transportedRemainderSource.compileExact value) entry).trans ?_
    apply (destination_graph coordinates ledger operations exactCode rows encode hm context event entry _).mp
    have codeEq := castMember_code operations exactCode (congrArg (fun whole => destinationContext context whole entry) same)
      ((result.transportedRemainderSource.compileExact value).destination entry)
    exact Eq.mpr (congrArg (fun code => r3 remainderMaterial 2
      (remainderInputEmbedding coordinates ledger operations rows encode ⟨context, event⟩) (ledger.entry context.1.2.1 entry) code) codeEq)
      (Classical.choose_spec ((remainderChecked coordinates ledger operations exactCode rows encode hm hw).destination context value entry)).1
  · funext entry
    refine (castCertification_origin operations context same (result.transportedRemainderSource.compileExact value) entry).trans ?_
    apply (origin_graph coordinates ledger operations exactCode rows encode hm context event entry _).mp
    have codeEq := castMember_code operations exactCode (congrArg (fun whole => originContext context whole entry) same)
      ((result.transportedRemainderSource.compileExact value).origin entry)
    exact Eq.mpr (congrArg (fun code => r3 remainderMaterial 3
      (remainderInputEmbedding coordinates ledger operations rows encode ⟨context, event⟩) (ledger.entry context.2 entry) code) codeEq)
      (Classical.choose_spec ((remainderChecked coordinates ledger operations exactCode rows encode hm hw).origin context value entry)).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact.WriteEncoding
