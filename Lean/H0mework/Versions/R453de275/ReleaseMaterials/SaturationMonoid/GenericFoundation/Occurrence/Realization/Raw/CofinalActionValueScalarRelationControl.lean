import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarRelationCoimage
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarCoimageControl

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

noncomputable section

/-- On the old true event, the generated relation boundary is zero in the
scalar relation quotient and nonzero in the already generated full coimage.
The original transferred row and next are unchanged. -/
theorem true_scalar_relation_coimage_residual_original_row_next :
    valueRelationProjection action (emitted toggle true)
      (integerToValueWords action
        (installedRelationAction action (emitted toggle true) trueRelation).1) = 0 ∧
    SourceGeneratedScalarPerfectification.canonicalMap
        (valueWordPairing action (emitted toggle true))
      (integerToValueWords action
        (installedRelationAction action (emitted toggle true) trueRelation).1) ≠ 0 ∧
    (¬ ∃ factor : valueRelationCompletion action (emitted toggle true) →ₗ[ℤ]
        valueWordCoimage action (emitted toggle true),
      factor.comp (valueRelationProjection action (emitted toggle true)) =
        SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing action (emitted toggle true))) ∧
    HEq (((valuePairingRoot action).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot action).toRoot.evolutionAt true).nextCurrent? = some true := by
  have boundaryZero := valueRelationProjection_old_boundary action
    (emitted toggle true) trueRelation
  have coimageNonzero : SourceGeneratedScalarPerfectification.canonicalMap
      (valueWordPairing action (emitted toggle true))
        (integerToValueWords action
          (installedRelationAction action (emitted toggle true) trueRelation).1) ≠ 0 := by
    intro zero
    have inPairingKernel : integerToValueWords action
        (installedRelationAction action (emitted toggle true) trueRelation).1 ∈
        LinearMap.ker (valueWordPairing action (emitted toggle true)) :=
      (Submodule.Quotient.mk_eq_zero _).1 zero
    rw [valueWordPairing_kernel_eq_evaluation_kernel] at inPairingKernel
    have readZero := (valueWordEvaluation_integer_square action
      (emitted toggle true) _).symm.trans inPairingKernel
    rw [true_boundary_source_value] at readZero
    exact one_ne_zero readZero
  have noFactor : ¬ ∃ factor : valueRelationCompletion action
      (emitted toggle true) →ₗ[ℤ] valueWordCoimage action (emitted toggle true),
      factor.comp (valueRelationProjection action (emitted toggle true)) =
        SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing action (emitted toggle true)) := by
    rintro ⟨factor, same⟩
    have atBoundary := LinearMap.congr_fun same
      (integerToValueWords action
        (installedRelationAction action (emitted toggle true) trueRelation).1)
    change factor (valueRelationProjection action (emitted toggle true)
        (integerToValueWords action
          (installedRelationAction action (emitted toggle true) trueRelation).1)) = _
      at atBoundary
    rw [boundaryZero, map_zero] at atBoundary
    exact coimageNonzero atBoundary.symm
  have old := generated_value_pairing_ledger_next action true
  exact ⟨boundaryZero, coimageNonzero, noFactor, old.2.2.1, old.2.2.2⟩

/-- The separate generator-only event genuinely allows relation/coimage
descent and recovers its original nonzero value. -/
theorem generator_scalar_relation_coimage_recovers_original_row_next :
    (∃ factor : valueRelationCompletion generatorOnlyAction
        (emitted toggle true) →ₗ[ℤ]
        valueWordCoimage generatorOnlyAction (emitted toggle true),
      factor.comp (valueRelationProjection generatorOnlyAction
        (emitted toggle true)) =
        SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing generatorOnlyAction (emitted toggle true))) ∧
    valueWordCoimageRecovery generatorOnlyAction (emitted toggle true)
        (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing generatorOnlyAction (emitted toggle true))
          (integerToValueWords generatorOnlyAction
            (Finsupp.single () (1 : ℤ)))) = 1 ∧
    HEq (((valuePairingRoot generatorOnlyAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot generatorOnlyAction).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  have compatible := (valueRelationCoimage_descent_iff generatorOnlyAction
    (emitted toggle true)).mpr (by
      intro relation
      exact generator_relations_sound relation.2)
  have old := generator_value_coimage_recovers_one_original_row_next
  exact ⟨compatible, old.1, old.2.2.1, old.2.2.2⟩

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
