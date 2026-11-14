import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairingDescent
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairingReducedControl
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionCochainConsumer
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionScalarPairingNonzeroControl

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

noncomputable section

private theorem nil_pairing_all_zero
    (left right : nilAction.Generator →₀ ℤ) :
    valuePairing nilAction (emitted toggle true) left right = 0 := by
  have leftRepr : left = Finsupp.single () (left ()) := by
    apply Finsupp.ext
    intro generator
    cases generator
    simp
  have rightRepr : right = Finsupp.single () (right ()) := by
    apply Finsupp.ext
    intro generator
    cases generator
    simp
  rw [leftRepr, rightRepr]
  have leftRead := (generated_single_equation nilAction true () (left ())).1
  have rightRead := (generated_single_equation nilAction true () (right ())).1
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (left ())) = (left ()) • (2 : ZMod 4) at leftRead
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (right ())) = (right ()) • (2 : ZMod 4) at rightRead
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (left ())) *
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (right ())) = 0
  rw [leftRead, rightRead]
  simp only [zsmul_eq_mul]
  have nil : (2 : ZMod 4) * 2 = 0 := by decide
  calc
    (↑(left ()) * (2 : ZMod 4)) * (↑(right ()) * 2) =
        (↑(left ()) * ↑(right ())) * (2 * 2) := by ring
    _ = 0 := by rw [nil, mul_zero]

private theorem nil_pairing_descends :
    ∃ factor : ((historyLaw nilAction).historyAt (emitted toggle true)).CompletionCarrier →ₗ[ℤ]
        ((nilAction.Generator →₀ ℤ) →ₗ[ℤ] ZMod 4),
      factor.comp ((historyLaw nilAction).historyAt (emitted toggle true)).completionProjection =
        valuePairingOnClosure nilAction (emitted toggle true) := by
  apply (valuePairing_descent_iff_boundary_zero nilAction true).mpr
  intro relation
  apply LinearMap.ext
  intro right
  exact nil_pairing_all_zero _ right

private theorem nil_evaluator_does_not_descend :
    ¬ ∃ factor : ((historyLaw nilAction).historyAt (emitted toggle true)).CompletionCarrier →ₗ[ℤ]
        ZMod 4,
      ∀ value : ((historyLaw nilAction).historyAt (emitted toggle true)).generatorClosure,
        factor (((historyLaw nilAction).historyAt (emitted toggle true)).completionProjection value) =
          ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation value.1 := by
  intro factor
  have killed := (generated_differential_descent_iff nilAction true).mpr factor
  have atRelation := killed (show
    ((historyLaw nilAction).historyAt (emitted toggle true)).relationClosure from
      trueRelation)
  have readsTwo :
      ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
        (installedRelationAction nilAction (emitted toggle true)
          (show ((historyLaw nilAction).historyAt (emitted toggle true)).relationClosure
            from trueRelation)).1 = 2 := by
    change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () 1) = 2
    exact (generated_single_equation nilAction true () 1).1
  rw [readsTwo] at atRelation
  exact (by decide : (2 : ZMod 4) ≠ 0) atRelation

theorem nil_pairing_quotient_cannot_recover_source :
    (∃ factor : ((historyLaw nilAction).historyAt (emitted toggle true)).CompletionCarrier →ₗ[ℤ]
        ((nilAction.Generator →₀ ℤ) →ₗ[ℤ] ZMod 4),
      factor.comp ((historyLaw nilAction).historyAt (emitted toggle true)).completionProjection =
        valuePairingOnClosure nilAction (emitted toggle true)) ∧
    (¬ ∃ factor : ((historyLaw nilAction).historyAt (emitted toggle true)).CompletionCarrier →ₗ[ℤ]
        ZMod 4,
      ∀ value : ((historyLaw nilAction).historyAt (emitted toggle true)).generatorClosure,
        factor (((historyLaw nilAction).historyAt (emitted toggle true)).completionProjection value) =
          ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation value.1) ∧
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (1 : ℤ)) ≠ 0 ∧
    HEq (((valuePairingRoot nilAction).toLedgerRoot.generatedLedgerAt true).entryDisposition
      (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot nilAction).toRoot.evolutionAt true).nextCurrent? = some true := by
  have old := nilpotent_pairing_loss_original_row_next
  exact ⟨nil_pairing_descends, nil_evaluator_does_not_descend,
    old.1, old.2.2.2.1, old.2.2.2.2⟩

theorem generator_nonzero_pairing_descends_original_row_next :
    (∃ factor : generatorHistory.CompletionCarrier →ₗ[ℤ]
        ((generatorOnlyAction.Generator →₀ ℤ) →ₗ[ℤ] ℤ),
      factor.comp generatorHistory.completionProjection =
        valuePairingOnClosure generatorOnlyAction (emitted toggle true)) ∧
    valuePairing generatorOnlyAction (emitted toggle true)
      (Finsupp.single () (1 : ℤ)) (Finsupp.single () (1 : ℤ)) = 1 ∧
    (valuePairingRoot generatorOnlyAction).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((valuePairingRoot generatorOnlyAction).emitted true) =
      .inl ⟨PUnit.unit, valuePairing generatorOnlyAction (emitted toggle true)⟩ ∧
    HEq (((valuePairingRoot generatorOnlyAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot generatorOnlyAction).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  obtain ⟨soundness, _⟩ := generator_pairing_from_receipt
  have evaluatorFactor : ∃ factor : generatorHistory.CompletionCarrier →ₗ[ℤ] ℤ,
      ∀ value : generatorHistory.generatorClosure,
        factor (generatorHistory.completionProjection value) =
          ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
            ).freeEvaluation value.1 := by
    exact ⟨((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).completionEvaluation soundness, fun _ => rfl⟩
  have descent := (valuePairing_descent_iff_evaluator_descent
    generatorOnlyAction true).mpr evaluatorFactor
  have one : valuePairing generatorOnlyAction (emitted toggle true)
      (Finsupp.single () (1 : ℤ)) (Finsupp.single () (1 : ℤ)) = 1 := by
    change ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).freeEvaluation (Finsupp.single () 1) *
      ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).freeEvaluation (Finsupp.single () 1) = 1
    have read := (generated_single_equation generatorOnlyAction true () 1).1
    change ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).freeEvaluation (Finsupp.single () 1) = 1 at read
    rw [read]
    norm_num
  have old := generated_value_pairing_ledger_next generatorOnlyAction true
  exact ⟨descent, one, old.1, old.2.2.1, old.2.2.2⟩

/-- The original nonzero Boolean relation is not erased by passing from
evaluator descent to pairing descent in the reduced integer value ring. -/
theorem true_nonzero_pairing_no_quotient_descent_original_row_next :
    (¬ ∃ factor : trueHistory.CompletionCarrier →ₗ[ℤ]
        ((action.Generator →₀ ℤ) →ₗ[ℤ] ℤ),
      factor.comp trueHistory.completionProjection =
        valuePairingOnClosure action (emitted toggle true)) ∧
    valuePairing action (emitted toggle true)
      (Finsupp.single () (1 : ℤ)) (Finsupp.single () (1 : ℤ)) = 1 ∧
    HEq (((valuePairingRoot action).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot action).toRoot.evolutionAt true).nextCurrent? = some true := by
  have noDescent : ¬ ∃ factor : trueHistory.CompletionCarrier →ₗ[ℤ]
      ((action.Generator →₀ ℤ) →ₗ[ℤ] ℤ),
    factor.comp trueHistory.completionProjection =
      valuePairingOnClosure action (emitted toggle true) := by
    intro pairingFactor
    obtain ⟨factor, reads⟩ :=
      (valuePairing_descent_iff_evaluator_descent action true).mp pairingFactor
    exact true_no_descended_evaluator ⟨factor.toAddMonoidHom, reads⟩
  have old := generated_value_pairing_ledger_next action true
  exact ⟨noDescent, integral_actual_pairing_one, old.2.2.1, old.2.2.2⟩

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
