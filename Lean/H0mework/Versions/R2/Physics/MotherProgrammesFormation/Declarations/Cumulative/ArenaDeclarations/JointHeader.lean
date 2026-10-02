import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.VocabularyCoverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.NetworkConsumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Consumer

/-! One rank material jointly forms the complete original network and
vocabulary. Targets occur only in coverage; no caller-generated header is
accepted by the source constructor. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaDeclarations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}

def vocabularyEncoding {V : ConstructiveRoot.Vocabulary.{0}}
    (encode : MotherVocabularyOrigin.Total V ↪ MotherArenaHigher.Base rank) :
    MotherArenaVocabulary.Encoding (rank := rank) V where
  current := (Function.Embedding.sigmaMk 0).trans encode
  anchor := (Function.Embedding.sigmaMk 1).trans encode
  incidence := (Function.Embedding.sigmaMk 2).trans encode
  lineage := (Function.Embedding.sigmaMk 3).trans encode
  native := (Function.Embedding.sigmaMk 4).trans encode
  relation := (Function.Embedding.sigmaMk 5).trans encode
  continued := (Function.Embedding.sigmaMk 6).trans encode
  redirect := (Function.Embedding.sigmaMk 7).trans encode
  terminal := (Function.Embedding.sigmaMk 8).trans encode
  cofinal := (Function.Embedding.sigmaMk 9).trans encode

theorem every_vocabulary_on_rank (V : ConstructiveRoot.Vocabulary.{0})
    (encode : MotherVocabularyOrigin.Total V ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ W : ConstructiveRoot.Vocabulary.{0},
      MotherArenaVocabulary.formVocabulary material = some W ∧ Nonempty (MotherVocabularyOrigin.Presentation V W) :=
  MotherArenaVocabulary.every_embedded_vocabulary V (vocabularyEncoding encode)

def formHeader (material : MotherArenaHigher.Material rank) :
    Option (WorldRelationNetwork.{0} × ConstructiveRoot.Vocabulary.{0}) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaNetwork.formNetwork parts.1).bind (fun network =>
    (MotherArenaVocabulary.formVocabulary parts.2).map (fun vocabulary => (network, vocabulary)))

theorem every_header (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0}) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
        formHeader material = some (G, W) ∧
        Nonempty (MotherNetworkOrigin.Presentation N G) ∧ Nonempty (MotherVocabularyOrigin.Presentation V W) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let Total := MotherNetworkOrigin.Total N ⊕ MotherVocabularyOrigin.Total V ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let networkAddress : MotherNetworkOrigin.Total N ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let vocabularyAddress : MotherVocabularyOrigin.Total V ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (shared.injective same))⟩
  obtain ⟨network, G, networkFormed, networkMap⟩ := MotherArenaNetworkOrigin.every_embedded_network N (.ofTotal networkAddress)
  obtain ⟨vocabulary, W, vocabularyFormed, vocabularyMap⟩ := MotherArenaVocabulary.every_embedded_vocabulary V (vocabularyEncoding vocabularyAddress)
  refine ⟨rank, MotherArenaHigher.pack rank (network, vocabulary), G, W, ?_, networkMap, vocabularyMap,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩
  simp only [formHeader, MotherArenaHigher.split_pack, networkFormed, Option.bind_some,
    vocabularyFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaDeclarations
