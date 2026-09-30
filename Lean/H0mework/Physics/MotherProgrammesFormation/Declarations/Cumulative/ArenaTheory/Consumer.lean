import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Coverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Admission
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Restriction

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherInventoryAdmission MotherAdmissionAlignment MotherJointWrite
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The original root's complete law surface and admission data enter the
same material at one sufficient rank. Every theory field then recovers from
that actual generated TheoryState by the full native restriction. -/
theorem every_original_law_surface (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) :
    let admission := root.source.eventInventoryAdmission
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank, ∃ value : SourcePair,
      ∃ n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1,
      ∃ v : MotherVocabularyOrigin.Presentation V (RepresentedV value),
      ∃ w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1,
      ∃ p : MotherNativeSourceOrigin.Presentation n v root.source.restructuringSource.source (Represented value).source,
      ∃ a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source,
      ∃ _represented : CompilerPresentation p root.source.restructuringSource.compiler.ledgerCompiler
        (Represented value).compiler.ledgerCompiler,
      ∃ _actual : CompilerPresentation a admission.actualSource.ledgerCompiler value.2.2.ledgerCompiler,
      ∃ generated : TheoryState value.1.1.1.1.1,
      ∃ theoryMap : MotherTheoryTransport.Presentation n root.source.lawSurface generated,
        formTheory material = some ⟨⟨value, AdmissionTransport.transportedData admission value n v w p a⟩, generated⟩ ∧
        theoryMap.restrictTheory = root.source.lawSurface ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let admission := root.source.eventInventoryAdmission
  let AllAddresses := MotherArenaAddressCoverage.RootAddressTotal root ⊕
    SourceWriteTotal admission.actualSource.ledgerCompiler ⊕ Total root.source.lawSurface ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let rootAddress : MotherArenaAddressCoverage.RootAddressTotal root ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let actualCode : SourceWriteTotal admission.actualSource.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let theoryCode : Total root.source.lawSurface ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  obtain ⟨parent, value, n, v, w, p, a, represented, actual, formed⟩ :=
    MotherArenaAdmission.admission_data_at_rank N V root admission rootAddress actualCode
  let transported := MotherTheoryTransport.transportedTheory n root.source.lawSurface
  let across := MotherTheoryTransport.transportedPresentation n root.source.lawSurface
  let encode := across.total.symm.toEmbedding.trans theoryCode
  obtain ⟨material, generated, generatedFormed, ⟨presentation⟩⟩ := every_theory_on_data parent value
    (AdmissionTransport.transportedData admission value n v w p a) formed transported encode
  let theoryMap := MotherTheoryTransport.formedPresentation n root.source.lawSurface presentation
  exact ⟨rank, material, value, n, v, w, p, a, represented, actual, generated, theoryMap,
    generatedFormed, theoryMap.restrictTheory_eq, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
