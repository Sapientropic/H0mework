import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaSource.Presentation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem network_check {net : M} {G : WorldRelationNetwork.{0}} (formed : formNetwork net = some G) :
    MotherArenaNetwork.Check net := by
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
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherArenaVocabulary.Presentation V W,
        formSource m = some ⟨G, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  obtain ⟨net, G, formedN, ⟨n⟩⟩ := MotherArenaNetworkOrigin.every_embedded_network N (MotherArenaNetworkOrigin.Encoding.ofTotal networkCode)
  have hn := network_check formedN
  have sameN : G = network net hn := Option.some.inj (formedN.symm.trans (network_formed net hn))
  cases sameN
  obtain ⟨base, W, formedV, ⟨v⟩⟩ := MotherArenaDeclarations.every_vocabulary_on_rank V vocabularyCode
  have hv := MotherArenaActual.vocabulary_check formedV
  have sameV : W = MotherArenaActual.V base hv :=
    Option.some.inj (formedV.symm.trans (MotherArenaActual.vocabulary_formed base hv))
  cases sameV
  obtain ⟨events, he⟩ := (MotherArenaHigher.read_surjective rank)
    (MotherArenaActual.Encoding.reader v original.toRootSource.actual eventCode)
  let ha := MotherArenaActual.Encoding.checked v original.toRootSource.actual eventCode he
  let a := MotherArenaActual.Encoding.presentation v original.toRootSource.actual eventCode he
  obtain ⟨fields, hf⟩ := (MotherArenaHigher.read_surjective rank) (AccountEncoding.reader n v original.toRootSource a)
  let graphs := AccountEncoding.graphs n v original.toRootSource a hf
  let compatible := AccountEncoding.compatible n v original.toRootSource a hf
  exact ⟨(MotherArenaHigher.pack rank) (net, (MotherArenaHigher.pack rank)
      (base, (MotherArenaHigher.pack rank) (events, fields))),
    network net hn, MotherArenaActual.V base hv,
    MotherNativeSourceOrigin.native (rootSource net base events fields hn hv ha graphs compatible), n, v,
    formed net base events fields hn hv ha graphs compatible,
    ⟨accountPresentation n v original a hf⟩⟩

abbrev Total {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (original : SourceNativeSource N V) :=
  MotherNetworkOrigin.Total N ⊕ MotherActualOrigin.Total V original.toRootSource.actual

theorem every_jointly_embedded_source (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (encode : Total original ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherArenaVocabulary.Presentation V W,
        formSource m = some ⟨G, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  let networkCode : MotherNetworkOrigin.Total N ↪ B :=
    ⟨fun x => encode (.inl x), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let vocabularyCode : MotherVocabularyOrigin.Total V ↪ B :=
    ⟨fun x => encode (.inr (.inl x)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (encode.injective same))⟩
  let eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B :=
    ⟨fun x => encode (.inr (.inr x)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (encode.injective same))⟩
  exact every_embedded_source N V original networkCode vocabularyCode eventCode

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
