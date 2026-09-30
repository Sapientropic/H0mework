import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.FullConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.SharedNetwork

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork MotherArenaSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- Both sides of an original admission reuse the same network material.
The rest of each source is formed by the original complete source factory. -/
def formSourceOnNetwork (net material : M) := MotherArenaSource.formSource ((MotherArenaHigher.pack rank) (net, material))

theorem every_source_on_network (net : M) (checked : MotherArenaNetwork.Check net)
    {N : WorldRelationNetwork.{0}} (n : MotherNetworkOrigin.Presentation N (network net checked))
    (V : ConstructiveRoot.Vocabulary.{0}) (original : SourceNativeSource N V)
    (vocabularyCode : MotherVocabularyOrigin.Total V ↪ B)
    (eventCode : Sigma original.toRootSource.actual.OccurrenceAt ↪ B) :
    ∃ material : M, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource (network net checked) W,
      ∃ v : MotherVocabularyOrigin.Presentation V W,
        formSourceOnNetwork net material = some ⟨network net checked, W, generated⟩ ∧ Nonempty (Presentation n v original generated) := by
  obtain ⟨base, W, formedV, ⟨v⟩⟩ := MotherArenaDeclarations.every_vocabulary_on_rank V vocabularyCode
  have hv := MotherArenaActual.vocabulary_check formedV
  have sameV : W = MotherArenaActual.V base hv :=
    Option.some.inj (formedV.symm.trans (MotherArenaActual.vocabulary_formed base hv))
  cases sameV
  obtain ⟨events, he⟩ := (MotherArenaHigher.read_surjective rank)
    (MotherArenaActual.Encoding.reader v original.toRootSource.actual eventCode)
  let ha := MotherArenaActual.Encoding.checked v original.toRootSource.actual eventCode he
  let a := MotherArenaActual.Encoding.presentation v original.toRootSource.actual eventCode he
  obtain ⟨fields, hf⟩ := (MotherArenaHigher.read_surjective rank) (MotherArenaSource.AccountEncoding.reader n v original.toRootSource a)
  let graphs := MotherArenaSource.AccountEncoding.graphs n v original.toRootSource a hf
  let compatible := MotherArenaSource.AccountEncoding.compatible n v original.toRootSource a hf
  exact ⟨(MotherArenaHigher.pack rank) (base, (MotherArenaHigher.pack rank) (events, fields)),
    MotherArenaActual.V base hv, MotherNativeSourceOrigin.native (rootSource net base events fields checked hv ha graphs compatible), v,
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
