import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaObligation.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
open MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open MotherPatchInventory MotherFullPatches MotherLedgerRoot MotherProjectionOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- All four original address operands are paid jointly at one source rank.
Every event/support/entry retains its full admitted obligation and native keys. -/
theorem every_law (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeLedgerRootClosure N V) (projection : SourceNativeProjectionLaw root.source)
    (old : SourceNativeLedgerRestructuringLaw root.source.source)
    :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
      ∃ generated : SourceNativeSource G W,
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
        ∃ a : Across p projection projectionLaw,
        ∃ base families : MotherArenaHigher.Material rank,
        ∃ ops : Operations (MotherArenaRestructuringVocabulary.formedSorts base) (MotherArenaRestructuringVocabulary.formedFamilies base families),
        ∃ sortMap : (index : Fin 12) → sortsOf old.vocabulary.base index ≃ MotherArenaRestructuringVocabulary.formedSorts base index,
        ∃ familyMap : FamilyMap sortMap (familiesOf old.vocabulary) (MotherArenaRestructuringVocabulary.formedFamilies base families),
        ∃ across : OperationsAcross sortMap familyMap (operationsOf old.vocabulary) ops,
          let law := sourceLaw (worldLaw p old) ops sortMap familyMap across
          formLaw material = some ⟨⟨⟨G, W, output⟩, projectionLaw⟩, law⟩ ∧
          (∀ choice point, projectionLaw.outcomeAt (a.projection choice) (pointEquiv p point).2 =
            a.outcomeEquiv choice point (projection.outcomeAt choice point.2)) ∧
          (∀ point : Point root.source.source, law.sourceEventAt (pointEquiv p point).2 = sortMap 0 (old.sourceEventAt point.2)) ∧
          (∀ (point : Point root.source.source) (support : N.Support) (entry : OpenResponsibilityAt N support),
            (obligationEquiv sortMap familyMap across).symm
              (law.obligationAt (pointEquiv p point).2 (n.ledger support entry)) = old.obligationAt point.2 entry) ∧
          (∀ point : Point root.source.source,
            output.source.ledgerCompiler.compilePatch (pointEquiv p point).2 =
              originalPatchAt p root.source.ledgerCompiler compiled q r s recover point) ∧
          (∀ current, (output.toRoot.evolutionAt (v.current current)).nextCurrent? =
            Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?) ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let SortTotal := Σ index, MotherRestructuringOrigin.sortsOf old.vocabulary.base index
  let FamilyTotal := MotherRestructuringOrigin.FamilyTotal (MotherRestructuringOrigin.familiesOf old.vocabulary)
  let AllAddresses := SourceWriteTotal root.source.ledgerCompiler ⊕ Total projection ⊕ SortTotal ⊕ FamilyTotal ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let rootCode : SourceWriteTotal root.source.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let projectionCode : Total projection ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let sortCode : SortTotal ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let familyCode : FamilyTotal ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inl value)))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same))))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr value)))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same))))⟩
  obtain ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    law, a, base, families, ops, sortMap, familyMap, across, formed, outcome, eventAt, obligationAt, patches, next⟩ :=
    law_at_rank N V root projection old rootCode projectionCode sortCode familyCode
  exact ⟨rank, material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    law, a, base, families, ops, sortMap, familyMap, across, formed, outcome, eventAt, obligationAt, patches, next,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
