import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The same sufficient rank pays the whole root and all four projection
carriers. Unselected active members and their complete payloads are retained. -/
theorem every_projection (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeLedgerRootClosure N V) (old : SourceNativeProjectionLaw root.source)
    :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
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
        ∃ projectionLaw : SourceNativeProjectionLaw output.source,
        ∃ a : Across p old projectionLaw,
          formProjection material = some ⟨⟨G, W, output⟩, projectionLaw⟩ ∧
          (∀ projection point, projectionLaw.outcomeAt (a.projection projection) (pointEquiv p point).2 =
            a.outcomeEquiv projection point (old.outcomeAt projection point.2)) ∧
          (∀ point : Point root.source.source,
            output.source.ledgerCompiler.compilePatch (pointEquiv p point).2 =
              originalPatchAt p root.source.ledgerCompiler compiled q r s recover point) ∧
          (∀ current, (output.toRoot.evolutionAt (v.current current)).nextCurrent? =
            Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?) ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := SourceWriteTotal root.source.ledgerCompiler ⊕ Total old ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let rootCode : SourceWriteTotal root.source.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let projectionCode : Total old ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (shared.injective same))⟩
  obtain ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    law, across, formed, outcome, patches, next⟩ := projection_at_rank N V root old rootCode projectionCode
  exact ⟨rank, material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    law, across, formed, outcome, patches, next, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
