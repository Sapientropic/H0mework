import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Presentation
import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem network_check {net : M} {G : WorldRelationNetwork.{0}} (formed : formNetwork net = some G) :
    MotherNetworkFactory.Check net := by
  unfold formNetwork at formed
  split at formed
  · assumption
  · cases formed

/-- Original inventories need no separate field table: their complete original
presentation is eliminated into the network's already formed whole ledger. -/
theorem every_embedded_source (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V)
    (networkCode : MotherNetworkOrigin.Total N ↪ B)
    (vocabularyCode : MotherVocabularyOrigin.Total V ↪ B)
    (eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
        formSource m = some ⟨G, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  obtain ⟨net, G, formedN, ⟨n⟩⟩ := MotherNetworkOrigin.every_jointly_embedded_network N networkCode
  have hn := network_check formedN
  have sameN : G = network net hn := Option.some.inj (formedN.symm.trans (network_formed net hn))
  cases sameN
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
  exact ⟨MotherHigherLawValue.pack (net, MotherHigherLawValue.pack
      (base, MotherHigherLawValue.pack (events, fields))),
    network net hn, MotherActualOrigin.V base hv,
    native (rootSource net base events fields hn hv ha graphs compatible), n, v,
    formed net base events fields hn hv ha graphs compatible,
    ⟨accountPresentation n v original a hf⟩⟩

abbrev Total {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (original : SourceNativeSource N V) :=
  MotherNetworkOrigin.Total N ⊕ MotherActualOrigin.Total V original.toRootSource.actual

theorem every_jointly_embedded_source (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (encode : Total original ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
        formSource m = some ⟨G, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  let networkCode : MotherNetworkOrigin.Total N ↪ B :=
    ⟨fun x => encode (.inl x), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let vocabularyCode : MotherVocabularyOrigin.Total V ↪ B :=
    ⟨fun x => encode (.inr (.inl x)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (encode.injective same))⟩
  let eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B :=
    ⟨fun x => encode (.inr (.inr x)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (encode.injective same))⟩
  exact every_embedded_source N V original networkCode vocabularyCode eventCode

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
