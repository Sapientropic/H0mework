import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.ActualCoverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.ActualOrigin.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- A complete original actual algebra enters the material factory with no
fixed-base address premise. All lawful events and full compiler payloads are
retained, including distinct events with the same compiler output. -/
theorem every_actual (Original : ConstructiveRoot.Vocabulary.{0}) (original : ActualEventAlgebra Original) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : ActualEventAlgebra W,
        ∃ p : MotherVocabularyOrigin.Presentation Original W, ∃ q : MotherActualOrigin.Presentation p original generated,
          formActual material = some ⟨W, generated⟩ ∧
          (∀ (current : Original.Current) (event : original.OccurrenceAt current),
            (p.evolution current).symm (generated.compile (q.event current event)) = original.compile event ∧
            (generated.compile (q.event current event)).kind = (original.compile event).kind ∧
            (generated.compile (q.event current event)).nextCurrent? =
              Option.map p.current (original.compile event).nextCurrent?) ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let Total := MotherActualOrigin.Total Original original ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let vocabularyCode : MotherVocabularyOrigin.Total Original ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inl.inj (shared.injective same))⟩
  let eventCode : Sigma original.OccurrenceAt ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inl.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨material, W, generated, p, formed, ⟨q⟩⟩ := every_embedded_actual Original original vocabularyCode eventCode
  refine ⟨rank, material, W, generated, p, q, formed, ?_, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩
  intro current event
  rw [q.compile_commutes]
  exact ⟨(p.evolution current).symm_apply_apply _, p.evolution_kind _, (p.evolution_next _).symm⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
