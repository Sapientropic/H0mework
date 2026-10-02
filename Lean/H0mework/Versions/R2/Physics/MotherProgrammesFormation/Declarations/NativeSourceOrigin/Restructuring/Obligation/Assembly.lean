import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.World

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherNetworkFactory MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms
open MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V}

theorem formed_law_consumes_original_maps (parent : M) (value : ProjectionValue)
    (parentFormed : formProjection parent = some value)
    {n : MotherNetworkOrigin.Presentation N value.1.1}
    {v : MotherVocabularyOrigin.Presentation V value.1.2.1}
    (p : MotherNativeSourceOrigin.Presentation n v original value.1.2.2.source.source)
    (old : SourceNativeLedgerRestructuringLaw original)
    (sortCode : (Σ index, sortsOf old.vocabulary.base index) ↪ B)
    (familyCode : FamilyTotal (familiesOf old.vocabulary) ↪ B) :
    ∃ material base families : M,
      ∃ ops : Operations (formedSorts base) (formedFamilies base families),
      ∃ sortMap : (index : Fin 12) → sortsOf old.vocabulary.base index ≃ formedSorts base index,
      ∃ familyMap : FamilyMap sortMap (familiesOf old.vocabulary) (formedFamilies base families),
      ∃ across : OperationsAcross sortMap familyMap (operationsOf old.vocabulary) ops,
        let law := sourceLaw (worldLaw p old) ops sortMap familyMap across
        formLaw material = some ⟨value, law⟩ ∧
        (∀ point : Point original, law.sourceEventAt (pointEquiv p point).2 = sortMap 0 (old.sourceEventAt point.2)) ∧
        (∀ (point : Point original) (support : N.Support) (entry : OpenResponsibilityAt N support),
          (obligationEquiv sortMap familyMap across).symm
            (law.obligationAt (pointEquiv p point).2 (n.ledger support entry)) = old.obligationAt point.2 entry) := by
  obtain ⟨vocabularyMaterial, base, families, ops, sortMap, familyMap, across, vocabularyFormed⟩ :=
    every_original_vocabulary old.vocabulary sortCode familyCode
  let law := sourceLaw (worldLaw p old) ops sortMap familyMap across
  obtain ⟨material, formed⟩ := every_law_on_formed_parent parent vocabularyMaterial value parentFormed law vocabularyFormed
  refine ⟨material, base, families, ops, sortMap, familyMap, across, formed, ?_, ?_⟩
  · exact fun point => congrArg (sortMap 0) (world_sourceEvent p old point)
  · intro point support entry
    exact (source_obligation_recovers (worldLaw p old) ops sortMap familyMap across (pointEquiv p point).2
      (n.ledger support entry)).trans (world_obligation p old point support entry)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
