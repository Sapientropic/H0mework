import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRestriction.Presentation
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
open MotherInventoryAdmission MotherAdmissionAlignment MotherArenaAdmission
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open MotherLedgerRoot MotherProjectionOrigin MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- A single sufficient rank and a single actual material form every field
of the original authority source. The complete native record is recovered
through the generated declaration, including the unselected source fibres. -/
theorem every_original_authority (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ value : SourcePair, ∃ data : PresentationData value,
      ∃ surface : TheoryState value.1.1.1.1.1,
      ∃ presentation : Presentation root.source value data surface,
        MotherArenaTheory.formTheory material = some ⟨⟨value, data⟩, surface⟩ ∧
        presentation.restrict = root.source ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let admission := root.source.eventInventoryAdmission
  let AllAddresses := MotherArenaAddressCoverage.RootAddressTotal root ⊕
    SourceWriteTotal admission.actualSource.ledgerCompiler ⊕ MotherArenaTheory.Total root.source.lawSurface ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let rootAddress : MotherArenaAddressCoverage.RootAddressTotal root ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let actualCode : SourceWriteTotal admission.actualSource.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let theoryCode : MotherArenaTheory.Total root.source.lawSurface ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
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
    projectionLaw, projectionAcross, base, families, ops, sortMap, familyMap, across,
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
  obtain ⟨declarationMaterial, formed⟩ := every_declaration_data pairMaterial value pairFormed
    (AdmissionTransport.transportedData admission value n v w p a)
  let transported := MotherTheoryTransport.transportedTheory n root.source.lawSurface
  let theoryAcross := MotherTheoryTransport.transportedPresentation n root.source.lawSurface
  let encode := theoryAcross.total.symm.toEmbedding.trans theoryCode
  obtain ⟨material, surface, generatedFormed, ⟨theoryPresentation⟩⟩ :=
    MotherArenaTheory.every_theory_on_data declarationMaterial value
      (AdmissionTransport.transportedData admission value n v w p a) formed transported encode
  let theoryMap := MotherTheoryTransport.formedPresentation n root.source.lawSurface theoryPresentation
  let ledgerMap := presentationOfPatches p old.ledgerCompiler compiled q r s recover
  let sourceMap := MotherRestructuringRestriction.presentationOfSections output p old ledgerMap
    projectionLaw ops sortMap familyMap across
  let presentation : Presentation root.source value
      (AdmissionTransport.transportedData admission value n v w p a) surface := {
    network := n
    vocabulary := v
    actualVocabulary := w
    represented := p
    actual := a
    actualCompiler := presentationOfPatches a admission.actualSource.ledgerCompiler
      actualCompiled actualQ actualR actualS actualRecover
    sortsOut := MotherArenaRestructuringVocabulary.formedSorts base
    familiesOut := MotherArenaRestructuringVocabulary.formedFamilies base families
    operations := ops
    sorts := sortMap
    families := familyMap
    across := across
    restructuring := sourceMap
    projection := projectionAcross
    theory := theoryMap
    data_eq := rfl }
  exact ⟨rank, material, value, _, surface, presentation, generatedFormed,
    presentation.restrict_eq, originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
