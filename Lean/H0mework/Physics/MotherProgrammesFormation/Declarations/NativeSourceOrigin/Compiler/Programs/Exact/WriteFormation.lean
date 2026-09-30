import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteReadback

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure WritePresentation {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (old generated : LedgerWriteRowSourceAt source operations.exactTransitionAt) where
  row : ∀ context, WriteEvents old context ≃ WriteEvents generated context
  remainder : ∀ context, RemainderEvents old context ≃ RemainderEvents generated context
  row_evolution : ∀ context event, generated.compileEvolution (row context event) = old.compileEvolution event
  row_exact : ∀ context event, generated.compileExact (row context event) = old.compileExact event
  remainder_compile : ∀ context event,
    (⟨generated.transportedRemainderSource.compileEvolution (remainder context event),
      generated.transportedRemainderSource.compileExact (remainder context event)⟩ : Sigma (WriteEncoding.Certification operations context)) =
    ⟨old.transportedRemainderSource.compileEvolution event, old.transportedRemainderSource.compileExact event⟩
  remainder_emit : ∀ context, Option.map (remainder context) (old.transportedRemainderSource.emit? context.1.2 context.2) =
    generated.transportedRemainderSource.emit? context.1.2 context.2

private theorem dependent_pair_eq {A : Type} {F : A → Type} {a b : A} {left : F a} {right : F b}
    (same : a = b) (valueEq : Eq.mp (congrArg F same) left = right) : (⟨a, left⟩ : Sigma F) = ⟨b, right⟩ := by
  cases same
  cases valueEq
  rfl

def WriteEncoding.presentation {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledger : LedgerCoordinates N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ B)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding rows)
    {rowMaterial remainderMaterial wholeMaterial : M}
    (hr : MotherHigherLawFormation.read rowMaterial = WriteEncoding.rowReader coordinates ledger operations exactCode rows encode)
    (hm : MotherHigherLawFormation.read remainderMaterial = WriteEncoding.remainderReader coordinates ledger operations exactCode rows encode)
    (hw : MotherHigherLawFormation.read wholeMaterial = WriteEncoding.wholeReader coordinates ledger operations rows encode) :
    WritePresentation rows (WriteEncoding.writeValue coordinates ledger operations exactCode rows encode hr hm hw) where
  row := WriteEncoding.rowEquiv coordinates ledger operations exactCode rows encode hr
  remainder := WriteEncoding.remainderEquiv coordinates ledger operations exactCode rows encode hm
  row_evolution := fun context event => congrArg Prod.fst (WriteEncoding.row_value coordinates ledger operations exactCode rows encode hr hm hw context event)
  row_exact := fun context event => congrArg Prod.snd (WriteEncoding.row_value coordinates ledger operations exactCode rows encode hr hm hw context event)
  remainder_compile := fun context event => dependent_pair_eq
    (WriteEncoding.whole_value coordinates ledger operations exactCode rows encode hr hm hw context event)
    (WriteEncoding.certification_value coordinates ledger operations exactCode rows encode hr hm hw context event)
  remainder_emit := WriteEncoding.remainder_emit coordinates ledger operations exactCode rows encode hm

theorem write_programs_formed (parent rowMaterial remainderMaterial wholeMaterial : M) (value : TransitionValue)
    (formed : formTransitions parent = some value) :
    let terminalParent := (MotherHigherLawValue.split parent).1
    let base := (MotherHigherLawValue.split terminalParent).1
    let terminalFormed := transitions_terminal_formed parent value.1 value.2.1 value.2.2.1 value.2.2.2 formed
    let compiledFormed := terminal_compilation_formed terminalParent value.1 value.2.1 value.2.2.1 terminalFormed
    let coordinates := coordinatesOfCompilation base value.1 value.2.1 compiledFormed
    let ledger := ledgerCoordinatesOfCompilation base value.1 value.2.1 compiledFormed
    let exactCode := exactCoordinatesOfTransitions parent value formed
    ∀ (rowCheck : WriteRowCheck coordinates ledger value.2.2.2 exactCode rowMaterial)
      (remainderCheck : RemainderCheck coordinates ledger value.2.2.2 exactCode remainderMaterial wholeMaterial),
      formWritePrograms (MotherHigherLawValue.pack (parent, MotherHigherLawValue.pack
        (rowMaterial, MotherHigherLawValue.pack (remainderMaterial, wholeMaterial)))) =
          some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2,
            generatedWriteSource coordinates ledger value.2.2.2 exactCode rowMaterial remainderMaterial wholeMaterial rowCheck remainderCheck⟩ := by
  dsimp only
  intro rowCheck remainderCheck
  unfold formWritePrograms
  simp only [MotherHigherLawValue.split_pack]
  unfold formWriteProgramParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨value, formed, ?_⟩
  exact (dif_pos rowCheck).trans (dif_pos remainderCheck)

abbrev WriteTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) :=
  Sigma (WriteEvents rows) ⊕ Sigma (RemainderEvents rows)

def WriteEncoding.ofTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} {rows : LedgerWriteRowSourceAt source operations.exactTransitionAt}
    (encode : WriteTotal rows ↪ B) : WriteEncoding rows where
  row := ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  remainder := ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩

/-- Complete original programs are covered by additional source material.
All prior formed source/compilation/terminal/transition values are retained. -/
theorem every_write_program (parent : M) (value : TransitionValue) (formed : formTransitions parent = some value)
    (rows : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt) (encode : WriteTotal rows ↪ B) :
    ∃ material : M, ∃ generated : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt,
      formWritePrograms material = some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2, generated⟩ ∧
      Nonempty (WritePresentation rows generated) := by
  let terminalParent := (MotherHigherLawValue.split parent).1
  let base := (MotherHigherLawValue.split terminalParent).1
  let terminalFormed := transitions_terminal_formed parent value.1 value.2.1 value.2.2.1 value.2.2.2 formed
  let compiledFormed := terminal_compilation_formed terminalParent value.1 value.2.1 value.2.2.1 terminalFormed
  let coordinates := coordinatesOfCompilation base value.1 value.2.1 compiledFormed
  let ledger := ledgerCoordinatesOfCompilation base value.1 value.2.1 compiledFormed
  let exactCode := exactCoordinatesOfTransitions parent value formed
  let code := WriteEncoding.ofTotal encode
  obtain ⟨rowMaterial, hr⟩ := MotherHigherLawFormation.read_surjective
    (WriteEncoding.rowReader coordinates ledger value.2.2.2 exactCode rows code)
  obtain ⟨remainderMaterial, hm⟩ := MotherHigherLawFormation.read_surjective
    (WriteEncoding.remainderReader coordinates ledger value.2.2.2 exactCode rows code)
  obtain ⟨wholeMaterial, hw⟩ := MotherHigherLawFormation.read_surjective
    (WriteEncoding.wholeReader coordinates ledger value.2.2.2 rows code)
  refine ⟨MotherHigherLawValue.pack (parent, MotherHigherLawValue.pack (rowMaterial,
    MotherHigherLawValue.pack (remainderMaterial, wholeMaterial))),
    WriteEncoding.writeValue coordinates ledger value.2.2.2 exactCode rows code hr hm hw, ?_,
    ⟨WriteEncoding.presentation coordinates ledger value.2.2.2 exactCode rows code hr hm hw⟩⟩
  exact write_programs_formed parent rowMaterial remainderMaterial wholeMaterial value formed
    (WriteEncoding.rowChecked coordinates ledger value.2.2.2 exactCode rows code hr)
    (WriteEncoding.remainderChecked coordinates ledger value.2.2.2 exactCode rows code hm hw)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
