import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Compiler

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original) (compiled : CompilationSection generated)
    {operations : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations)
    {rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt}
    (r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows)
    {terminal : LedgerTerminalRowSourceAt generated}
    (s : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal)
    (recover : ∀ point : Point original,
      (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2)

include recover in
theorem compilation_image (point : Point original) :
    fullCompilationEquiv p point.2 (compiler.compile point.2) = compiled (pointEquiv p point) :=
  (congrArg (fullCompilationEquiv p point.2) (recover point)).symm.trans
    ((fullCompilationEquiv p point.2).apply_symm_apply _)

def originalPatchAt (point : Point original) :
    SourceNativeFiniteLedgerPatchAt generated operations.exactTransitionAt rows terminal
      (compiled (pointEquiv p point)) :=
  (Equiv.cast (congrArg (SourceNativeFiniteLedgerPatchAt generated operations.exactTransitionAt rows terminal)
    (compilation_image p compiler compiled recover point)))
      (fullPatch p q r s point (compiler.compile point.2) (compiler.compilePatch point.2))

def originalPatchSection : PatchSection ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩ :=
  Equiv.piCongrLeft _ (pointEquiv p) (originalPatchAt p compiler compiled q r s recover)

theorem originalPatchSection_at (point : Point original) :
    originalPatchSection p compiler compiled q r s recover (pointEquiv p point) =
      originalPatchAt p compiler compiled q r s recover point :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

/-- The original compiler is used only in coverage. All its programmes and
full compilation values first enter one actual material output; its entire
patch section is transported to that very output before source formation. -/
theorem formed_source_consumes_original_full_compiler (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceWriteTotal compiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
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
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r,
      formed, recover, _row, _remainder, _selected⟩ :=
    formed_source_recovers_original_programmes N V original compiler encode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p compiler compiled q r s recover
  obtain ⟨material, compilerFormed, sourceFormed⟩ := every_ledger_source_from_programmes parent value formed patches
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    compilerFormed, sourceFormed, originalPatchSection_at p compiler compiled q r s recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
