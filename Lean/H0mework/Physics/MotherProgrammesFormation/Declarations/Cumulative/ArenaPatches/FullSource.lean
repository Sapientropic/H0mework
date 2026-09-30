import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Complete patch formation uses the same literal source and adequate rank
as all of the original programmes. No additional address space is needed. -/
theorem compiler_on_source {rank : Ordinal.{0}}
    {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original)
    (parent : MotherArenaHigher.Material rank)
    (sourceFormed : MotherArenaSource.formSource parent = some ⟨G, W, generated⟩)
    (encode : SourceWriteTotal compiler ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
      ∃ recover : ∀ point : Point original,
        (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2,
        let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
        let patches := originalPatchSection p compiler compiled q r s recover
        let full := compilerOfPatches value patches
        formCompiler material = some ⟨value, full⟩ ∧
        formLedgerSource material = some ⟨G, W, ⟨generated, full⟩⟩ ∧
        (∀ point : Point original,
          full.compilePatch (pointEquiv p point).2 = originalPatchAt p compiler compiled q r s recover point) := by
  obtain ⟨programmeMaterial, compiled, terminal, operations, rows, s, q, r, formed, recover⟩ :=
    MotherArenaExact.programmes_on_source p compiler parent sourceFormed encode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p compiler compiled q r s recover
  obtain ⟨material, compilerFormed, sourceFormed⟩ := every_ledger_source_from_programmes programmeMaterial value formed patches
  exact ⟨material, compiled, terminal, operations, rows, s, q, r, recover,
    compilerFormed, sourceFormed, originalPatchSection_at p compiler compiled q r s recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
