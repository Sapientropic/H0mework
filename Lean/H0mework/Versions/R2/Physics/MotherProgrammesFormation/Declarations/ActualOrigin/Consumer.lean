import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.ActualOrigin.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev Total (Original : Vocabulary.{0}) (original : ActualEventAlgebra Original) :=
  MotherVocabularyOrigin.Total Original ⊕ Sigma original.OccurrenceAt

/-- A single joint address covers both the original full vocabulary and every
event, including distinct events whose full compiler outputs coincide. -/
theorem every_jointly_embedded_actual (Original : Vocabulary.{0}) (original : ActualEventAlgebra Original)
    (encode : Total Original original ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0}, ∃ generated : ActualEventAlgebra W,
      ∃ p : MotherVocabularyOrigin.Presentation Original W,
        formActual m = some ⟨W, generated⟩ ∧ Nonempty (Presentation p original generated) := by
  let vocabularyCode : MotherVocabularyOrigin.Total Original ↪ B :=
    ⟨fun x => encode (.inl x), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let eventCode : Sigma original.OccurrenceAt ↪ B :=
    ⟨fun x => encode (.inr x), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  exact every_embedded_actual Original original vocabularyCode eventCode

theorem formed_actual_restores_full_original_compile
    (Original : Vocabulary.{0}) (original : ActualEventAlgebra Original)
    (encode : Total Original original ↪ B) :
    ∃ m : M, ∃ W : Vocabulary.{0}, ∃ generated : ActualEventAlgebra W,
      ∃ p : MotherVocabularyOrigin.Presentation Original W, ∃ q : Presentation p original generated,
        formActual m = some ⟨W, generated⟩ ∧
        ∀ (c : Original.Current) (event : original.OccurrenceAt c),
          (p.evolution c).symm (generated.compile (q.event c event)) = original.compile event ∧
          (generated.compile (q.event c event)).kind = (original.compile event).kind ∧
          (generated.compile (q.event c event)).nextCurrent? =
            Option.map p.current (original.compile event).nextCurrent? := by
  obtain ⟨m, W, generated, p, formed, ⟨q⟩⟩ := every_jointly_embedded_actual Original original encode
  refine ⟨m, W, generated, p, q, formed, ?_⟩
  intro c event
  rw [q.compile_commutes]
  exact ⟨(p.evolution c).symm_apply_apply _, p.evolution_kind _, (p.evolution_next _).symm⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
