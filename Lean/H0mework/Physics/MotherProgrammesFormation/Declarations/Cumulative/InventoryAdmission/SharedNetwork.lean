import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Body

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherNativeSourceOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Both sides of an original admission reuse the same network material.
The rest of each source is formed by the original complete source factory. -/
def formSourceOnNetwork (net material : M) := formSource (MotherHigherLawValue.pack (net, material))

theorem every_source_on_network (net : M) (checked : MotherNetworkFactory.Check net)
    {N : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N (network net checked))
    (V : ConstructiveRoot.Vocabulary.{0}) (original : SourceNativeSource N V)
    (vocabularyCode : MotherVocabularyOrigin.Total V ↪ B)
    (eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B) :
    ∃ material : M, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource (network net checked) W,
      ∃ v : MotherVocabularyOrigin.Presentation V W,
        formSourceOnNetwork net material = some ⟨network net checked, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  obtain ⟨base, W, formedV, ⟨v⟩⟩ := MotherVocabularyOrigin.every_jointly_embedded_vocabulary V vocabularyCode
  have hv := MotherActualOrigin.vocabulary_check formedV
  have sameV : W = MotherActualOrigin.V base hv :=
    Option.some.inj (formedV.symm.trans (MotherActualOrigin.vocabulary_formed base hv))
  cases sameV
  obtain ⟨events, he⟩ := MotherHigherLawFormation.read_surjective
    (MotherActualOrigin.Encoding.reader v original.toRootSource.actual eventCode)
  let ha := MotherActualOrigin.Encoding.checked v original.toRootSource.actual eventCode he
  let a := MotherActualOrigin.Encoding.presentation v original.toRootSource.actual eventCode he
  obtain ⟨fields, hf⟩ := MotherHigherLawFormation.read_surjective (AccountEncoding.reader n v original.toRootSource a)
  let graphs := AccountEncoding.graphs n v original.toRootSource a hf
  let compatible := AccountEncoding.compatible n v original.toRootSource a hf
  exact ⟨MotherHigherLawValue.pack (base, MotherHigherLawValue.pack (events, fields)),
    MotherActualOrigin.V base hv, native (rootSource net base events fields checked hv ha graphs compatible), v,
    formed net base events fields checked hv ha graphs compatible, ⟨accountPresentation n v original a hf⟩⟩

theorem every_source_on_network_value (net : M) {N G : WorldRelationNetwork.{0}}
    (formedNet : formNetwork net = some G) (n : MotherNetworkOrigin.Presentation N G)
    (V : ConstructiveRoot.Vocabulary.{0}) (original : SourceNativeSource N V)
    (vocabularyCode : MotherVocabularyOrigin.Total V ↪ B)
    (eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B) :
    ∃ material : M, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ v : MotherVocabularyOrigin.Presentation V W,
        formSourceOnNetwork net material = some ⟨G, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  have checked := network_check formedNet
  have same : G = network net checked := Option.some.inj (formedNet.symm.trans (network_formed net checked))
  cases same
  exact every_source_on_network net checked n V original vocabularyCode eventCode

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
