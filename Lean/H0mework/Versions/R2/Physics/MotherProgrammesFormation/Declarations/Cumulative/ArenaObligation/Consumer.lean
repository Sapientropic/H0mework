import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaObligation.Assembly
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
open MotherArenaNetwork MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open MotherJointWrite MotherPatchInventory MotherFullPatches MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherObligationOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- One material forms the original registration law together with the
complete original root/compiler and projection. Every event, support and
entry retains its full admitted obligation, and the original patch/next
exchange is inherited from that same root output. -/
theorem law_at_rank (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeLedgerRootClosure N V) (projection : SourceNativeProjectionLaw root.source)
    (old : SourceNativeLedgerRestructuringLaw root.source.source)
    (rootCode : SourceWriteTotal root.source.ledgerCompiler ↪ B) (projectionCode : Total projection ↪ B)
    (sortCode : (Σ index, sortsOf old.vocabulary.base index) ↪ B)
    (familyCode : FamilyTotal (familiesOf old.vocabulary) ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
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
        ∃ base families : M,
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
            Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?) := by
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    projectionLaw, a, parentFormed, outcomeAt, patchAt, nextAt⟩ :=
    MotherArenaProjection.projection_at_rank N V root projection rootCode projectionCode
  obtain ⟨material, base, families, ops, sortMap, familyMap, across, formed, eventAt, obligationAt⟩ :=
    formed_law_consumes_original_maps parent _ parentFormed p old sortCode familyCode
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    projectionLaw, a, base, families, ops, sortMap, familyMap, across,
    formed, outcomeAt, eventAt, obligationAt, patchAt, nextAt⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
