import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.NativeCompiler
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Recovery

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherInventoryAdmission MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open MotherLedgerRoot MotherProjectionOrigin MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- A caller-independent material factory is covered at a chosen sufficient
rank. Downstream law-surface and handoff carriers may share this same rank. -/
theorem admission_data_at_rank {rank : Ordinal.{0}} (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V)
    (admission : SourceNativeCompleteEventInventoryAdmission root.source.restructuringSource)
    (rootAddress : MotherArenaAddressCoverage.RootAddressTotal root ↪ MotherArenaHigher.Base rank)
    (actualCode : SourceWriteTotal admission.actualSource.ledgerCompiler ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ value : SourcePair,
      ∃ n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1,
      ∃ v : MotherVocabularyOrigin.Presentation V (RepresentedV value),
      ∃ w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1,
      ∃ p : MotherNativeSourceOrigin.Presentation n v root.source.restructuringSource.source (Represented value).source,
      ∃ a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source,
      ∃ _represented : CompilerPresentation p root.source.restructuringSource.compiler.ledgerCompiler
        (Represented value).compiler.ledgerCompiler,
      ∃ _actual : CompilerPresentation a admission.actualSource.ledgerCompiler value.2.2.ledgerCompiler,
        formDeclarationData material = some ⟨value, AdmissionTransport.transportedData admission value n v w p a⟩ := by
  let old := root.source.restructuringSource.compiler
  let rootCode : SourceWriteTotal old.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => rootAddress (.inl value), fun _ _ same => Sum.inl.inj (rootAddress.injective same)⟩
  let projectionCode : Total root.source.projectionLaw ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => rootAddress (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (rootAddress.injective same))⟩
  let sortCode : (Σ index, sortsOf old.restructuringLaw.vocabulary.base index) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => rootAddress (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (rootAddress.injective same)))⟩
  let familyCode : FamilyTotal (familiesOf old.restructuringLaw.vocabulary) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => rootAddress (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (rootAddress.injective same)))⟩
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, rows, n, v, p, s, q, r, recover,
    projectionLaw, _projectionAcross, base, families, ops, sortMap, familyMap, across,
    parentFormed, _sourceFormed, _compilerEq, _outcome, _obligations, _certificates, _patches, _next⟩ :=
    MotherArenaReceipts.restructuring_at_rank N V root rootCode projectionCode sortCode familyCode
  let programme : WriteProgramValue := ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩
  let full := compilerOfPatches programme (originalPatchSection p old.ledgerCompiler compiled q r s recover)
  let output := representedRoot root.toLedgerRoot p full recover
  let law := sourceLaw (worldLaw p old.restructuringLaw) ops sortMap familyMap across
  let lawValue : LawValue := ⟨⟨⟨G, W, output⟩, projectionLaw⟩, law⟩
  let certificates := MotherRestructuringReceipts.completeCertificateSection p old compiled recover ops sortMap familyMap across
  let represented : MotherRestructuringReceipts.CompilerValue :=
    ⟨lawValue, MotherRestructuringReceipts.compilerOf lawValue certificates⟩
  obtain ⟨pairMaterial, U, actual, w, a, actualCompiled, actualTerminal, actualOperations, actualRows,
    actualS, actualQ, actualR, actualRecover, pairFormed, _actualPatch⟩ :=
    every_actual_source parent represented parentFormed n admission.ActualV admission.actualSource.source
      admission.actualSource.ledgerCompiler actualCode
  let actualProgramme : WriteProgramValue := ⟨⟨G, U, actual⟩, actualCompiled, actualTerminal, actualOperations, actualRows⟩
  let actualFull := compilerOfPatches actualProgramme
    (originalPatchSection a admission.actualSource.ledgerCompiler actualCompiled actualQ actualR actualS actualRecover)
  let value : SourcePair := ⟨represented, U, ⟨actual, actualFull⟩⟩
  obtain ⟨material, formed⟩ := every_declaration_data pairMaterial value pairFormed
    (AdmissionTransport.transportedData admission value n v w p a)
  exact ⟨material, value, n, v, w, p, a,
    presentationOfPatches p old.ledgerCompiler compiled q r s recover,
    presentationOfPatches a admission.actualSource.ledgerCompiler actualCompiled actualQ actualR actualS actualRecover,
    formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
