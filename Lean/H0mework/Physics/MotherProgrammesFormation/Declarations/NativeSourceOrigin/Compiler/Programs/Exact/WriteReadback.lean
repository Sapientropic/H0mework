import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.RemainderEncoding

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms.WriteEncoding
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledger : LedgerCoordinates N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ B)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding rows)

theorem remainder_emit {material : M}
    (hm : MotherHigherLawFormation.read material = remainderReader coordinates ledger operations exactCode rows encode)
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

def writeValue {rowMaterial remainderMaterial wholeMaterial : M}
    (hr : MotherHigherLawFormation.read rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : MotherHigherLawFormation.read remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : MotherHigherLawFormation.read wholeMaterial = wholeReader coordinates ledger operations rows encode) :
    LedgerWriteRowSourceAt source operations.exactTransitionAt :=
  generatedWriteSource coordinates ledger operations exactCode rowMaterial remainderMaterial wholeMaterial
    (rowChecked coordinates ledger operations exactCode rows encode hr)
    (remainderChecked coordinates ledger operations exactCode rows encode hm hw)

section
variable {rowMaterial remainderMaterial wholeMaterial : M}
    (hr : MotherHigherLawFormation.read rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : MotherHigherLawFormation.read remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : MotherHigherLawFormation.read wholeMaterial = wholeReader coordinates ledger operations rows encode)

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

def castMember {left right : WriteContext source} (same : left = right) (value : operations.Exact left) : operations.Exact right :=
  Eq.mp (congrArg operations.Exact same) value

theorem castMember_code {left right : WriteContext source} (same : left = right) (value : operations.Exact left) :
    exactCode right (castMember operations same value) = exactCode left value := by
  cases same
  rfl

abbrev Certification (context : RemainderContext source) (whole : LedgerWriteEvolutionAt N ⟨context.1.2.1⟩ ⟨context.2⟩) :=
  ExactLedgerWriteCertificationAt N ⟨context.1.2.1⟩ ⟨context.2⟩ (operations.exactTransitionAt context.1.2) whole

def castCertification (context : RemainderContext source)
    {left right : LedgerWriteEvolutionAt N ⟨context.1.2.1⟩ ⟨context.2⟩}
    (same : left = right) (value : Certification operations context left) : Certification operations context right :=
  Eq.mp (congrArg (Certification operations context) same) value

theorem castCertification_destination (context : RemainderContext source)
    {left right : LedgerWriteEvolutionAt N ⟨context.1.2.1⟩ ⟨context.2⟩}
    (same : left = right) (value : Certification operations context left) (entry : OpenResponsibilityAt N context.1.2.1) :
    (castCertification operations context same value).destination entry =
      castMember operations (congrArg (fun whole => destinationContext context whole entry) same) (value.destination entry) := by
  cases same
  rfl

theorem castCertification_origin (context : RemainderContext source)
    {left right : LedgerWriteEvolutionAt N ⟨context.1.2.1⟩ ⟨context.2⟩}
    (same : left = right) (value : Certification operations context left) (entry : OpenResponsibilityAt N context.2) :
    (castCertification operations context same value).origin entry =
      castMember operations (congrArg (fun whole => originContext context whole entry) same) (value.origin entry) := by
  cases same
  rfl

theorem certification_ext (context : RemainderContext source)
    {whole : LedgerWriteEvolutionAt N ⟨context.1.2.1⟩ ⟨context.2⟩}
    (left right : Certification operations context whole)
    (destination : left.destination = right.destination) (origin : left.origin = right.origin) : left = right := by
  cases left
  cases right
  cases destination
  cases origin
  rfl

theorem certification_value {rowMaterial remainderMaterial wholeMaterial : M}
    (hr : MotherHigherLawFormation.read rowMaterial = rowReader coordinates ledger operations exactCode rows encode)
    (hm : MotherHigherLawFormation.read remainderMaterial = remainderReader coordinates ledger operations exactCode rows encode)
    (hw : MotherHigherLawFormation.read wholeMaterial = wholeReader coordinates ledger operations rows encode)
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms.WriteEncoding
