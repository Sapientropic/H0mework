import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.FullSource

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Any original complete compiler enters one source-generated material
at a sufficient rank, including its actual full branch-indexed patch. -/
theorem every_ledger_source (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
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
          full.compilePatch (pointEquiv p point).2 = originalPatchAt p compiler compiled q r s recover point) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := SourceWriteTotal compiler ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let encode : SourceWriteTotal compiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let sourceCode : MotherNativeSourceOrigin.Total original ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => encode (.inl (.inl (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨parent, G, W, generated, n, v, formedSource, ⟨p⟩⟩ :=
    MotherArenaSource.every_jointly_embedded_source N V original sourceCode
  obtain ⟨material, compiled, terminal, operations, rows, s, q, r, recover, compilerFormed, sourceFormed, patch⟩ :=
    compiler_on_source p compiler parent formedSource encode
  exact ⟨rank, material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    compilerFormed, sourceFormed, patch, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
