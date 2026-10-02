import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Native

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
open MotherInventoryAdmission MotherAdmissionAlignment MotherArenaAdmission
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherPatchInventory MotherFullPatches
open MotherLedgerRoot MotherProjectionOrigin MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- All original small carrier operands for a complete authority root.
This total is used only to choose one adequate material rank in coverage. -/
abbrev AddressTotal {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) :=
  MotherArenaAddressCoverage.RootAddressTotal root ⊕
    SourceWriteTotal root.source.eventInventoryAdmission.actualSource.ledgerCompiler ⊕
    MotherArenaTheory.Total root.source.lawSurface ⊕ MotherNetworkFactory.B

abbrev FormationAt (rank : Ordinal.{0}) {N : WorldRelationNetwork.{0}}
    {V : ConstructiveRoot.Vocabulary.{0}} (root : SourceNativeAuthoritativeRootClosure N V) : Prop :=
    ∃ material : MotherArenaHigher.Material rank,
      ∃ value : SourcePair, ∃ data : PresentationData value,
      ∃ surface : TheoryState value.1.1.1.1.1,
      ∃ presentation : Presentation root value data surface,
        MotherArenaTheory.formTheory material = some ⟨⟨value, data⟩, surface⟩ ∧
        presentation.restrict = root ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress)

/-- The actual whole source and all-current emitter form at any one
sufficient rank; dependent families can therefore share a single rank. -/
theorem root_at_rank {rank : Ordinal.{0}} (N : WorldRelationNetwork.{0})
    (V : ConstructiveRoot.Vocabulary.{0}) (root : SourceNativeAuthoritativeRootClosure N V)
    (shared : AddressTotal root ↪ MotherArenaHigher.Base rank) : FormationAt rank root := by
  let admission := root.source.eventInventoryAdmission
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
  let presentation : MotherAuthorityRestriction.Presentation root.source value
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
  let rootPresentation : Presentation root value
      (AdmissionTransport.transportedData admission value n v w p a) surface := {
    toPresentation := presentation
    emitted_eq := by
      intro current
      change (p.event current).symm (emitterEquiv p root.emitted (v.current current)) = root.emitted current
      rw [emitter_at]
      exact (p.event current).symm_apply_apply _ }
  exact ⟨material, value, _, surface, rootPresentation, generatedFormed,
    rootPresentation.restrict_eq, originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

/-- Coverage chooses one sufficient rank from the complete original fields;
no address condition is exported to the original reality contract. -/
theorem every_original_root (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) : ∃ rank, FormationAt rank root :=
  ⟨MotherArenaHigher.carrierRank (AddressTotal root),
    root_at_rank N V root (MotherArenaHigher.carrierAddress (AddressTotal root))⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
