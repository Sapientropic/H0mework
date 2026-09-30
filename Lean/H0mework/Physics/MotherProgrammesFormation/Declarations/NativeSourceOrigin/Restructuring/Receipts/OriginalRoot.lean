import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.SectionsAcross

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open MotherJointWrite MotherPatchInventory MotherFullPatches MotherLedgerRoot MotherProjectionOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

abbrev OriginalRootFormation (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) : Prop :=
    let old := root.source.restructuringSource.compiler
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
      ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v root.source.restructuringSource.source generated,
      ∃ s : TerminalPresentation (transportedTerminal p old.ledgerCompiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler old.ledgerCompiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q old.ledgerCompiler.writeRowSource) rows,
      ∃ recover : ∀ point : Point root.source.restructuringSource.source,
        (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = old.ledgerCompiler.compile point.2,
        let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
        let patches := originalPatchSection p old.ledgerCompiler compiled q r s recover
        let full := compilerOfPatches value patches
        let output := representedRoot root.toLedgerRoot p full recover
        ∃ projectionLaw : SourceNativeProjectionLaw output.source,
        ∃ a : Across p root.source.projectionLaw projectionLaw,
        ∃ base families : M,
        ∃ ops : Operations (formedSorts base) (formedFamilies base families),
        ∃ sortMap : (index : Fin 12) → sortsOf old.restructuringLaw.vocabulary.base index ≃ formedSorts base index,
        ∃ familyMap : FamilyMap sortMap (familiesOf old.restructuringLaw.vocabulary) (formedFamilies base families),
        ∃ across : OperationsAcross sortMap familyMap (operationsOf old.restructuringLaw.vocabulary) ops,
          let law := sourceLaw (worldLaw p old.restructuringLaw) ops sortMap familyMap across
          let lawValue : LawValue := ⟨⟨⟨G, W, output⟩, projectionLaw⟩, law⟩
          let certificates := completeCertificateSection p old compiled recover ops sortMap familyMap across
          let compiler := compilerOf lawValue certificates
          formRestructuringCompiler material = some ⟨lawValue, compiler⟩ ∧
          formRestructuringSource material = some ⟨G, W, sourceOf ⟨lawValue, compiler⟩⟩ ∧
          compiler.ledgerCompiler = output.source.ledgerCompiler ∧
          (∀ choice point, projectionLaw.outcomeAt (a.projection choice) (pointEquiv p point).2 =
            a.outcomeEquiv choice point (root.source.projectionLaw.outcomeAt choice point.2)) ∧
          (∀ (point : Point root.source.restructuringSource.source) (support : N.Support) (entry : OpenResponsibilityAt N support),
            (obligationEquiv sortMap familyMap across).symm
              (law.obligationAt (pointEquiv p point).2 (n.ledger support entry)) = old.restructuringLaw.obligationAt point.2 entry) ∧
          (∀ point : Point root.source.restructuringSource.source,
            (completeCertificateAtEquiv p old compiled recover ops sortMap familyMap across point).symm
              (compiler.certifyRestructuring (pointEquiv p point).2) = old.certifyRestructuring point.2) ∧
          (∀ point : Point root.source.restructuringSource.source,
            compiler.ledgerCompiler.compilePatch (pointEquiv p point).2 = originalPatchAt p old.ledgerCompiler compiled q r s recover point) ∧
          (∀ current, (output.toRoot.evolutionAt (v.current current)).nextCurrent? =
            Option.map v.current (root.toRoot.evolutionAt current).nextCurrent?)

/-- The original admitted authoritative root enters only coverage. One
material forms its complete restructuring source, full compiler and every
original certification, together with its root and projection representation. -/
theorem formed_restructuring_consumes_original_root (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V)
    (rootCode : SourceWriteTotal root.source.restructuringSource.compiler.ledgerCompiler ↪ B)
    (projectionCode : Total root.source.projectionLaw ↪ B)
    (sortCode : (Σ index, sortsOf root.source.restructuringSource.compiler.restructuringLaw.vocabulary.base index) ↪ B)
    (familyCode : FamilyTotal (familiesOf root.source.restructuringSource.compiler.restructuringLaw.vocabulary) ↪ B) :
    OriginalRootFormation N V root := by
  let old := root.source.restructuringSource.compiler
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    projectionLaw, a, base, families, ops, sortMap, familyMap, across, formed, outcomeAt, _eventAt, obligationAt, patchAt, nextAt⟩ :=
    formed_law_consumes_original_root N V root.toLedgerRoot root.source.projectionLaw old.restructuringLaw
      rootCode projectionCode sortCode familyCode
  let value : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let patches := originalPatchSection p old.ledgerCompiler compiled q r s recover
  let full := compilerOfPatches value patches
  let output := representedRoot root.toLedgerRoot p full recover
  let law := sourceLaw (worldLaw p old.restructuringLaw) ops sortMap familyMap across
  let lawValue : LawValue := ⟨⟨⟨G, W, output⟩, projectionLaw⟩, law⟩
  let certificates : LawCertification lawValue := completeCertificateSection p old compiled recover ops sortMap familyMap across
  obtain ⟨material, compilerFormed, sourceFormed⟩ := every_compiler_on_formed_law parent lawValue formed certificates
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    projectionLaw, a, base, families, ops, sortMap, familyMap, across,
    compilerFormed, sourceFormed, rfl, outcomeAt, obligationAt,
    completeCertificateSection_recovers p old compiled recover ops sortMap familyMap across, patchAt, nextAt⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
