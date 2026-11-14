import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionScalarPairing
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionCochainConsumer

/-!
# The same Boolean source tests generated and forbidden scalar pairings

The false receipt kills its relations and obtains the actual quotient pairing
from its generated evaluation. The true receipt has a nonzero relation image,
so the source projection records no quotient pairing and inherits the exact
unsound residual. Both retain the original transfer row and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

theorem false_pairing_from_receipt :
    ∃ soundness : GeneratedRelationSoundnessAt
        ((faithfulLaw action).faithfulAt (emitted toggle false)),
      scalarPairing? action (emitted toggle false) =
        some (rankOnePairing
          (((faithfulLaw action).faithfulAt (emitted toggle false)
            ).completionEvaluation soundness)) := by
  have branch := (scalarPairing_source_branch action false).2.1
  generalize outcome_eq :
    ((faithfulLaw action).faithfulAt (emitted toggle false)).settleRelations = outcome at branch
  cases outcome with
  | sound soundness =>
      exact ⟨soundness, branch.1⟩
  | unsound obstruction =>
      obtain ⟨relation, nonzero⟩ := branch.2
      exact False.elim (nonzero (false_free_evaluation_zero _))

theorem true_pairing_absent_from_receipt :
    scalarPairing? action (emitted toggle true) = none := by
  have branch := (scalarPairing_source_branch action true).2.1
  generalize outcome_eq :
    ((faithfulLaw action).faithfulAt (emitted toggle true)).settleRelations = outcome at branch
  cases outcome with
  | sound soundness =>
      exact False.elim (true_not_relationsSound soundness.sound)
  | unsound _ =>
      exact branch.1

theorem false_pairing_original_row_next :
    ∃ soundness : GeneratedRelationSoundnessAt
        ((faithfulLaw action).faithfulAt (emitted toggle false)),
      (scalarPairingRoot action).source.projectionLaw.outcomeAt
          (.component PUnit.unit) ((scalarPairingRoot action).emitted false) =
        .inl ⟨PUnit.unit, some (rankOnePairing
          (((faithfulLaw action).faithfulAt (emitted toggle false)
            ).completionEvaluation soundness))⟩ ∧
      HEq (((scalarPairingRoot action).toLedgerRoot.generatedLedgerAt false
          ).entryDisposition (entry toggle false))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred false
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt (network toggle)
                (entry toggle false) (entry toggle false))) ∧
      ((scalarPairingRoot action).toRoot.evolutionAt false).nextCurrent? =
        some false := by
  obtain ⟨soundness, generated⟩ := false_pairing_from_receipt
  refine ⟨soundness, ?_,
    (scalarPairing_inventory_ledger_next action false).2.1,
    (scalarPairing_inventory_ledger_next action false).2.2⟩
  have installed := (scalarPairing_source_branch action false).1
  rw [generated] at installed
  exact installed

theorem true_no_free_pairing_original_row_next :
    (scalarPairingRoot action).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((scalarPairingRoot action).emitted true) =
      .inl ⟨PUnit.unit, none⟩ ∧
    (¬ ∃ factor : trueHistory.CompletionCarrier →+ ℤ,
      ∀ value : trueHistory.generatorClosure,
        factor (trueHistory.completionProjection value) =
          ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
            value.1) ∧
    HEq (((scalarPairingRoot action).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network toggle)
              (entry toggle true) (entry toggle true))) ∧
    ((scalarPairingRoot action).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  refine ⟨?_, true_no_descended_evaluator,
    (scalarPairing_inventory_ledger_next action true).2.1,
    (scalarPairing_inventory_ledger_next action true).2.2⟩
  have installed := (scalarPairing_source_branch action true).1
  rw [true_pairing_absent_from_receipt] at installed
  exact installed

#print axioms false_pairing_original_row_next
#print axioms true_no_free_pairing_original_row_next

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
