import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem formed_source_restores_original_events_and_inventory
    (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0}) (original : SourceNativeSource N V)
    (encode : Total original ↪ B) :
    ∃ m : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
        ∃ p : Presentation n v original generated,
          formSource m = some ⟨G, W, generated⟩ ∧
          ∀ (c : V.Current) (event : original.toRootSource.actual.OccurrenceAt c),
            (v.evolution c).symm (generated.toRootSource.actual.compile (p.event c event)) =
              original.toRootSource.actual.compile event ∧
            (generated.toRootSource.actual.compile (p.event c event)).nextCurrent? =
              Option.map v.current (original.toRootSource.actual.compile event).nextCurrent? ∧
            (∀ member : original.law.AffectedInventoryAt event.2,
              (p.inventory event).symm (p.inventory event member) = member) ∧
            (∀ member : generated.law.AffectedInventoryAt (p.event c event).2,
              p.inventory event ((p.inventory event).symm member) = member) := by
  obtain ⟨m, G, W, generated, n, v, formed, ⟨p⟩⟩ := every_jointly_embedded_source N V original encode
  refine ⟨m, G, W, generated, n, v, p, formed, ?_⟩
  intro c event
  refine ⟨?_, ?_, (p.inventory event).symm_apply_apply, (p.inventory event).apply_symm_apply⟩
  · rw [p.compile_eq, Equiv.symm_apply_apply]
  · rw [p.compile_eq]
    exact (v.evolution_next _).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
