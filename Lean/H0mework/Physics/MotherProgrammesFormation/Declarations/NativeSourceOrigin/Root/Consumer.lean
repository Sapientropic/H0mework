import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Root

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- Same-material formation reaches the original root constructor. The full
source/compiler/patch declaration and all-current emitter are retained; the
old root appears only in this coverage theorem. -/
theorem formed_root_consumes_original_root (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (root : SourceNativeLedgerRootClosure N V) (encode : SourceWriteTotal root.source.ledgerCompiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v root.source.source generated,
      ∃ s : TerminalPresentation (transportedTerminal p root.source.ledgerCompiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler root.source.ledgerCompiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q root.source.ledgerCompiler.writeRowSource) rows,
      ∃ recover : ∀ point : Point root.source.source,
        (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = root.source.ledgerCompiler.compile point.2,
        let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
        let patches := originalPatchSection p root.source.ledgerCompiler compiled q r s recover
        let full := compilerOfPatches value patches
        let output := representedRoot root p full recover
        formRoot material = some ⟨G, W, output⟩ ∧
        (∀ point : Point root.source.source,
          output.source.ledgerCompiler.compilePatch (pointEquiv p point).2 =
            originalPatchAt p root.source.ledgerCompiler compiled q r s recover point) ∧
        (∀ current,
          (⟨output.emitted (v.current current), output.generatedLedgerAt (v.current current)⟩ :
            Σ event : generated.toRootSource.actual.OccurrenceAt (v.current current), SourceNativeLedgerEvolutionAt generated event) =
              ⟨p.event current (root.emitted current), fullCompilationEquiv p (root.emitted current) (root.generatedLedgerAt current)⟩) ∧
        (∀ current, (output.toRoot.evolutionAt (v.current current)).nextCurrent? =
          Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?) := by
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
      compilerFormed, _sourceFormed, patchesAt⟩ :=
    formed_source_consumes_original_full_compiler N V root.source.source root.source.ledgerCompiler encode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p root.source.ledgerCompiler compiled q r s recover
  let full := compilerOfPatches value patches
  have commutes : RootCheck ⟨value, full⟩ (emitterEquiv p root.emitted) :=
    representedCompiler_commutes root p full recover
  obtain ⟨material, rootFormed⟩ := every_emitted_section parent ⟨value, full⟩ compilerFormed (emitterEquiv p root.emitted) commutes
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    rootFormed, patchesAt, generatedLedgerAt_pair root p full recover, generated_next root p full recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
