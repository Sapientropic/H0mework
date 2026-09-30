import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteReadback
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteFormation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

private theorem dependent_pair_eq {A : Type} {F : A → Type} {a b : A} {left : F a} {right : F b}
    (same : a = b) (valueEq : Eq.mp (congrArg F same) left = right) : (⟨a, left⟩ : Sigma F) = ⟨b, right⟩ := by
  cases same
  cases valueEq
  rfl

def WriteEncoding.presentation {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ B)
    (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt) (encode : WriteEncoding (rank := rank) rows)
    {rowMaterial remainderMaterial wholeMaterial : MotherArenaHigher.Material rank}
    (hr : (MotherArenaHigher.read rank) rowMaterial = WriteEncoding.rowReader coordinates ledger operations exactCode rows encode)
    (hm : (MotherArenaHigher.read rank) remainderMaterial = WriteEncoding.remainderReader coordinates ledger operations exactCode rows encode)
    (hw : (MotherArenaHigher.read rank) wholeMaterial = WriteEncoding.wholeReader coordinates ledger operations rows encode) :
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
    let terminalParent := ((MotherArenaHigher.split rank) parent).1
    let base := ((MotherArenaHigher.split rank) terminalParent).1
    let terminalFormed := transitions_terminal_formed parent value.1 value.2.1 value.2.2.1 value.2.2.2 formed
    let compiledFormed := terminal_compilation_formed terminalParent value.1 value.2.1 value.2.2.1 terminalFormed
    let coordinates := MotherArenaPrograms.coordinatesOfCompilation base value.1 value.2.1 compiledFormed
    let ledger := MotherArenaPrograms.ledgerCoordinatesOfCompilation base value.1 value.2.1 compiledFormed
    let exactCode := exactCoordinatesOfTransitions parent value formed
    ∀ (rowCheck : WriteRowCheck coordinates ledger value.2.2.2 exactCode rowMaterial)
      (remainderCheck : RemainderCheck coordinates ledger value.2.2.2 exactCode remainderMaterial wholeMaterial),
      formWritePrograms ((MotherArenaHigher.pack rank) (parent, (MotherArenaHigher.pack rank)
        (rowMaterial, (MotherArenaHigher.pack rank) (remainderMaterial, wholeMaterial)))) =
          some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2,
            generatedWriteSource coordinates ledger value.2.2.2 exactCode rowMaterial remainderMaterial wholeMaterial rowCheck remainderCheck⟩ := by
  dsimp only
  intro rowCheck remainderCheck
  unfold formWritePrograms
  simp only [MotherArenaHigher.split_pack]
  unfold formWriteProgramParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨value, formed, ?_⟩
  exact (dif_pos rowCheck).trans (dif_pos remainderCheck)

def WriteEncoding.ofTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} {rows : LedgerWriteRowSourceAt source operations.exactTransitionAt}
    (encode : WriteTotal rows ↪ B) : WriteEncoding (rank := rank) rows where
  row := ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  remainder := ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩

/-- Complete original programs are covered by additional source material.
All prior formed source/compilation/terminal/transition values are retained. -/
theorem every_write_program (parent : M) (value : TransitionValue) (formed : formTransitions parent = some value)
    (rows : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt) (encode : WriteTotal rows ↪ B) :
    ∃ material : M, ∃ generated : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt,
      formWritePrograms material = some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2, generated⟩ ∧
      Nonempty (WritePresentation rows generated) := by
  let terminalParent := ((MotherArenaHigher.split rank) parent).1
  let base := ((MotherArenaHigher.split rank) terminalParent).1
  let terminalFormed := transitions_terminal_formed parent value.1 value.2.1 value.2.2.1 value.2.2.2 formed
  let compiledFormed := terminal_compilation_formed terminalParent value.1 value.2.1 value.2.2.1 terminalFormed
  let coordinates := MotherArenaPrograms.coordinatesOfCompilation base value.1 value.2.1 compiledFormed
  let ledger := MotherArenaPrograms.ledgerCoordinatesOfCompilation base value.1 value.2.1 compiledFormed
  let exactCode := exactCoordinatesOfTransitions parent value formed
  let code := WriteEncoding.ofTotal encode
  obtain ⟨rowMaterial, hr⟩ := (MotherArenaHigher.read_surjective rank)
    (WriteEncoding.rowReader coordinates ledger value.2.2.2 exactCode rows code)
  obtain ⟨remainderMaterial, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (WriteEncoding.remainderReader coordinates ledger value.2.2.2 exactCode rows code)
  obtain ⟨wholeMaterial, hw⟩ := (MotherArenaHigher.read_surjective rank)
    (WriteEncoding.wholeReader coordinates ledger value.2.2.2 rows code)
  refine ⟨(MotherArenaHigher.pack rank) (parent, (MotherArenaHigher.pack rank) (rowMaterial,
    (MotherArenaHigher.pack rank) (remainderMaterial, wholeMaterial))),
    WriteEncoding.writeValue coordinates ledger value.2.2.2 exactCode rows code hr hm hw, ?_,
    ⟨WriteEncoding.presentation coordinates ledger value.2.2.2 exactCode rows code hr hm hw⟩⟩
  exact write_programs_formed parent rowMaterial remainderMaterial wholeMaterial value formed
    (WriteEncoding.rowChecked coordinates ledger value.2.2.2 exactCode rows code hr)
    (WriteEncoding.remainderChecked coordinates ledger value.2.2.2 exactCode rows code hm hw)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
