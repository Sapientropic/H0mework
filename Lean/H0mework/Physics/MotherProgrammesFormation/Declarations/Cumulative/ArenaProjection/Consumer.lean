import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.Formation
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches MotherLedgerRoot
open MotherPatchInventory
open MotherProjectionOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- Original root and projection data occur only in coverage. The same
material forms the full original root representation and every projection
fibre, while the original classifier and dependent projector both commute. -/
theorem projection_at_rank (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeLedgerRootClosure N V) (old : SourceNativeProjectionLaw root.source)
    (rootCode : SourceWriteTotal root.source.ledgerCompiler ↪ B) (projectionCode : Total old ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
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
            Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?) := by
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    rootFormed, patchAt, _ledgerAt, nextAt⟩ := MotherArenaRoot.root_at_rank N V root rootCode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p root.source.ledgerCompiler compiled q r s recover
  let full := compilerOfPatches value patches
  let output := representedRoot root p full recover
  let pulled : SourceNativeProjectionLaw output.source := pullbackLaw (left := root.source) (right := output.source) p old
  let across : Across p old pulled := pullbackAcross (left := root.source) (right := output.source) p old
  let encode : Total pulled ↪ B := across.totalEquiv.symm.toEmbedding.trans projectionCode
  obtain ⟨material, law, formed, ⟨presentation⟩⟩ :=
    every_projection_on_formed_root parent ⟨G, W, output⟩ rootFormed pulled encode
  let combined := across.comp presentation
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    law, combined, formed, combined.outcome_eq, patchAt, nextAt⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
