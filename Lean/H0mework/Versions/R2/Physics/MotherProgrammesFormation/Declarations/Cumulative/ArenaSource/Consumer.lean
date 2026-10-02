import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaSource.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- All original source data enter one rank-material factory. The joint
address and target source are used only to prove coverage; neither is an
input of formSource. Complete original inventories retain both inverse maps. -/
theorem every_source (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (original : SourceNativeSource N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
        ∃ generated : SourceNativeSource G W,
          ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
            ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
              formSource material = some ⟨G, W, generated⟩ ∧
              (∀ (current : V.Current) (event : original.toRootSource.actual.OccurrenceAt current),
                (v.evolution current).symm (generated.toRootSource.actual.compile (p.event current event)) =
                  original.toRootSource.actual.compile event ∧
                (generated.toRootSource.actual.compile (p.event current event)).nextCurrent? =
                  Option.map v.current (original.toRootSource.actual.compile event).nextCurrent? ∧
                (∀ member : original.law.AffectedInventoryAt event.2,
                  (p.inventory event).symm (p.inventory event member) = member) ∧
                (∀ member : generated.law.AffectedInventoryAt (p.event current event).2,
                  p.inventory event ((p.inventory event).symm member) = member)) ∧
              ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
                Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                  (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := MotherNativeSourceOrigin.Total original ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let address : Total original ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨material, G, W, generated, n, v, formed, ⟨p⟩⟩ := every_jointly_embedded_source N V original address
  refine ⟨rank, material, G, W, generated, n, v, p, formed, ?_, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩
  intro current event
  refine ⟨?_, ?_, (p.inventory event).symm_apply_apply, (p.inventory event).apply_symm_apply⟩
  · rw [p.compile_eq, Equiv.symm_apply_apply]
  · rw [p.compile_eq]
    exact (v.evolution_next _).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaSource
