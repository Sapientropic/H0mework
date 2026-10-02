import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.SharedNetwork

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open MotherPatchInventory MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original)

theorem compilation_on_source (parent : M) (formed : MotherNativeSourceOrigin.formSource parent = some ⟨G, W, generated⟩) :
    ∃ material : M, ∃ compiled : CompilationSection generated,
      formCompilation material = some ⟨⟨G, W, generated⟩, compiled⟩ ∧
      ∀ point : Point original, (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2 := by
  obtain ⟨coordinates, sourceFormed⟩ := coordinates_generated parent ⟨G, W, generated⟩ formed
  let compiled := compilationSectionEquiv p (originalCompilations compiler)
  obtain ⟨targetMaterial, targets, targetFormed, targetEq⟩ :=
    every_target_section parent ⟨G, W, generated⟩ coordinates sourceFormed (sectionTargets generated compiled)
  cases targetEq
  obtain ⟨material, ledgers, wholeFormed, wholeEq⟩ := every_whole_section targetMaterial ⟨G, W, generated⟩ coordinates
    (sectionTargets generated compiled) targetFormed (sectionLedgers generated compiled)
  refine ⟨material, compiled, ?_, full_original_compilation_recovers p compiler⟩
  rw [formCompilation, wholeFormed, Option.map_some, wholeEq]
  dsimp only
  rw [compilationFromSection]

theorem programmes_on_source (parent : M) (formed : MotherNativeSourceOrigin.formSource parent = some ⟨G, W, generated⟩)
    (encode : SourceWriteTotal compiler ↪ B) :
    ∃ material : M, ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ _s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ _r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
        formWritePrograms material = some ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩ ∧
        ∀ point : Point original, (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2 := by
  let terminalCode : TerminalTotal compiler.terminalRowSource ↪ B :=
    ⟨fun value => encode (.inl (.inl (.inr value))), fun _ _ same => Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))⟩
  let operationCode : TransitionTotal (Transitions.ofCompiler compiler) ↪ B :=
    ⟨fun value => encode (.inl (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inl.inj (encode.injective same))⟩
  let writeCode : WriteTotal (operations := Transitions.ofCompiler compiler) compiler.writeRowSource ↪ B :=
    ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  obtain ⟨compilationMaterial, compiled, compilationFormed, recover⟩ := compilation_on_source p compiler parent formed
  obtain ⟨terminalMaterial, terminal, terminalFormed, ⟨s⟩⟩ := every_terminal_program compilationMaterial ⟨G, W, generated⟩ compiled
    compilationFormed (transportedTerminal p compiler.terminalRowSource)
    ((terminalTotalEquiv p compiler.terminalRowSource).symm.toEmbedding.trans terminalCode)
  obtain ⟨operationMaterial, operations, operationFormed, ⟨q⟩⟩ := every_transition_program terminalMaterial ⟨G, W, generated⟩
    compiled terminal terminalFormed (transportedTransitions p (Transitions.ofCompiler compiler))
    ((transitionTotalEquiv p (Transitions.ofCompiler compiler)).symm.toEmbedding.trans operationCode)
  obtain ⟨material, rows, rowsFormed, ⟨r⟩⟩ := every_write_program operationMaterial
    ⟨⟨G, W, generated⟩, compiled, terminal, operations⟩ operationFormed (sourceWrite p q compiler.writeRowSource)
    ((totalEquiv p q compiler.writeRowSource).symm.toEmbedding.trans writeCode)
  exact ⟨material, compiled, terminal, operations, rows, s, q, r, rowsFormed, recover⟩

theorem full_compiler_on_source (parent : M) (formed : MotherNativeSourceOrigin.formSource parent = some ⟨G, W, generated⟩)
    (encode : SourceWriteTotal compiler ↪ B) :
    ∃ material : M, ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
      ∃ recover : ∀ point : Point original, (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2,
        let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
        let patches := originalPatchSection p compiler compiled q r s recover
        let full := compilerOfPatches value patches
        formCompiler material = some ⟨value, full⟩ ∧
        formLedgerSource material = some ⟨G, W, ⟨generated, full⟩⟩ ∧
        (∀ point : Point original, full.compilePatch (pointEquiv p point).2 = originalPatchAt p compiler compiled q r s recover point) := by
  obtain ⟨programmes, compiled, terminal, operations, rows, s, q, r, programmeFormed, recover⟩ := programmes_on_source p compiler parent formed encode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p compiler compiled q r s recover
  obtain ⟨material, compilerFormed, sourceFormed⟩ := every_ledger_source_from_programmes programmes value programmeFormed patches
  exact ⟨material, compiled, terminal, operations, rows, s, q, r, recover, compilerFormed, sourceFormed,
    originalPatchSection_at p compiler compiled q r s recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
