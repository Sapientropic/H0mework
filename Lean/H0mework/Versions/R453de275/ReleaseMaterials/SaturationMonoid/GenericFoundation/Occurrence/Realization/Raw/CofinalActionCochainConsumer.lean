import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionCochain
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionRegression

/-!
# Original Boolean receipt consumes its installed relation differential

The true event writes a relation boundary that the old completion kills, but
the same event's evaluator sends it to one. The old faithful classifier must
therefore retain a nonzero unsound residual. Both dependent faces are installed
at that event on the original raw root, with its original row and next.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

open CofinalRelationGeneratedComplex
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

abbrev trueHistory := (historyLaw action).historyAt (emitted toggle true)

def trueRelation : trueHistory.relationClosure :=
  ⟨Finsupp.single () (1 : ℤ), true_basis_relation_mem⟩

theorem true_relation_installed_boundary :
    ((natComplex trueHistory).d 0 1).hom =
      installedRelationAction action (emitted toggle true) ∧
    trueHistory.completionProjection
      (installedRelationAction action (emitted toggle true) trueRelation) = 0 := by
  have exact := generated_cochain_kernel_exact action true
  refine ⟨exact.1, (exact.2 _).2 ?_⟩
  exact ⟨trueRelation, rfl⟩

theorem true_boundary_source_value :
    ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      (installedRelationAction action (emitted toggle true) trueRelation).1 = 1 := by
  change ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
    (Finsupp.single () 1) = 1
  exact true_actual_equation

/-- A zero completion class has nonzero actual evaluation. The installed
differential and installed unsound residual are read at the same root event;
the complete old ledger and generated next remain the original ones. -/
theorem true_event_cochain_residual_consumer :
    ((natComplex trueHistory).d 0 1).hom =
        installedRelationAction action (emitted toggle true) ∧
      trueHistory.completionProjection
        (installedRelationAction action (emitted toggle true) trueRelation) = 0 ∧
      ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
        (installedRelationAction action (emitted toggle true) trueRelation).1 = 1 ∧
      (cochainRoot action).source.projectionLaw.outcomeAt
          (.component PUnit.unit) ((cochainRoot action).emitted true) =
        .inl ⟨PUnit.unit,
          installedRelationAction action (emitted toggle true)⟩ ∧
      ∃ obstruction : GeneratedUnsoundRelationObstructionAt
          ((faithfulLaw action).faithfulAt (emitted toggle true)),
        ∃ coordinate : GeneratedRelationResidualCoordinateAt
            ((faithfulLaw action).faithfulAt (emitted toggle true)),
          (cochainRoot action).source.projectionLaw.outcomeAt
            (.inherited (.component PUnit.unit))
            ((cochainRoot action).emitted true) =
              .inl ⟨PUnit.unit, .unsound obstruction coordinate⟩ ∧
          coordinate.coordinate ≠ 0 ∧
          HEq (((cochainRoot action).toLedgerRoot.generatedLedgerAt true
              ).entryDisposition (entry toggle true))
            (LedgerEntryDispositionAt.evolved
              (LedgerEntryEvolutionAt.transferred true
                rfl rfl (Nat.le_refl _) :
                  LedgerEntryEvolutionAt (network toggle)
                    (entry toggle true) (entry toggle true))) ∧
          ((cochainRoot action).toRoot.evolutionAt true).nextCurrent? =
            some true := by
  obtain ⟨obstruction, coordinate, oldResidual, nonzero, _oldRow, _oldNext⟩ :=
    true_event_installed_unsound
  have installed := generated_cochain_residual_ledger_next action true
  refine ⟨true_relation_installed_boundary.1,
    true_relation_installed_boundary.2,
    true_boundary_source_value, installed.1,
    obstruction, coordinate, ?_, nonzero, installed.2.2.1, installed.2.2.2⟩
  exact oldResidual

/-- The original evaluator cannot descend through the source-generated
completion: the installed boundary is zero there and has value one before
compression. This excludes a free quotient recovery at this exact event. -/
theorem true_no_descended_evaluator :
    ¬ ∃ factor : trueHistory.CompletionCarrier →+ ℤ,
      ∀ value : trueHistory.generatorClosure,
        factor (trueHistory.completionProjection value) =
          ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
            value.1 := by
  rintro ⟨factor, factors⟩
  have killed := (generated_differential_descent_iff action true).2
    (show ∃ linearFactor : trueHistory.CompletionCarrier →ₗ[ℤ] ℤ,
      ∀ value : trueHistory.generatorClosure,
        linearFactor (trueHistory.completionProjection value) =
          ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation value.1
      from ⟨factor.toIntLinearMap, factors⟩)
  have atRelation := killed trueRelation
  rw [true_boundary_source_value] at atRelation
  norm_num at atRelation

theorem false_event_still_reads_zero :
    ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
      (Finsupp.single () 1) = 0 :=
  false_actual_equation

theorem false_free_evaluation_zero (word : Unit →₀ ℤ) :
    ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
      word = 0 := by
  induction word using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add left right left_ih right_ih =>
      calc
        ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
            (left + right) =
          ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation left +
            ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation right :=
          map_add _ left right
        _ = 0 := by rw [left_ih, right_ih, add_zero]
  | single generator coefficient =>
      cases generator
      have scaled : (Finsupp.single () coefficient : Unit →₀ ℤ) =
          coefficient • Finsupp.single () (1 : ℤ) := by simp
      calc
        ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
            (Finsupp.single () coefficient) =
          ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
            (coefficient • Finsupp.single () 1) := congrArg _ scaled
        _ = coefficient •
            ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
              (Finsupp.single () 1) := map_smul _ coefficient _
        _ = 0 := by rw [false_actual_equation, smul_zero]

/-- The false event has a genuine descended quotient evaluator. It is the
same fixed dynamic and the same installed differential law as the true
counterexample; only the source receipt's evaluator changed. -/
theorem false_event_descends :
    ∃ factor : ((historyLaw action).historyAt (emitted toggle false)).CompletionCarrier
        →ₗ[ℤ] ℤ,
      ∀ value : ((historyLaw action).historyAt (emitted toggle false)).generatorClosure,
        factor (((historyLaw action).historyAt (emitted toggle false)
          ).completionProjection value) =
          ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
            value.1 := by
  apply (generated_differential_descent_iff action false).1
  intro relation
  exact false_free_evaluation_zero _

theorem nonemitted_true_cannot_activate_false :
    (eventPresentation toggle false).forward true ≠
      (cochainRoot action).emitted false :=
  same_current_receipts_distinct.2.2

#print axioms true_relation_installed_boundary
#print axioms true_boundary_source_value
#print axioms true_event_cochain_residual_consumer
#print axioms true_no_descended_evaluator
#print axioms false_event_still_reads_zero
#print axioms false_free_evaluation_zero
#print axioms false_event_descends
#print axioms nonemitted_true_cannot_activate_false

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
