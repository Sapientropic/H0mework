import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPrograms.TerminalFormation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.TerminalConsumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
open MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The adequate rank is selected once from the full original source and
both complete terminal event families. The compiler and programmes use that
same source, preserving unselected events as well as the selected output. -/
theorem every_terminal (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
        ∃ compiled : CompilationSection generated, ∃ rows : LedgerTerminalRowSourceAt generated,
          ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
            ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
              ∃ _q : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) rows,
                formTerminalSource material = some ⟨⟨G, W, generated⟩, compiled, rows⟩ ∧
                (∀ point : Point original,
                  (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) ∧
                ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
                  Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                    (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := SourceTerminalTotal compiler ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let sourceCode : MotherNativeSourceOrigin.Total original ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inl.inj (shared.injective same))⟩
  let eventCode : TerminalTotal compiler.terminalRowSource ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inl.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨sourceMaterial, G, W, generated, n, v, sourceFormed, ⟨p⟩⟩ :=
    MotherArenaSource.every_jointly_embedded_source N V original sourceCode
  obtain ⟨parent, compiled, formed, recover⟩ :=
    MotherArenaCompiler.compilation_on_source p compiler sourceMaterial sourceFormed
  let generatedCode := (terminalTotalEquiv p compiler.terminalRowSource).symm.toEmbedding.trans eventCode
  obtain ⟨material, rows, rowsFormed, ⟨q⟩⟩ := every_terminal_program parent ⟨G, W, generated⟩ compiled formed
    (transportedTerminal p compiler.terminalRowSource) generatedCode
  exact ⟨rank, material, G, W, generated, compiled, rows, n, v, p, q, rowsFormed, recover,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
