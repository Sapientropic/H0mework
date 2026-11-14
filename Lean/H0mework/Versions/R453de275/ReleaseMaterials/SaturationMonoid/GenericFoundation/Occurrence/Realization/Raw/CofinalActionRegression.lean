import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

open CofinalHistorySettlement
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

/-- Both events inhabit the same original event fibre. The emitter selects
the event at its current; the other fibre member cannot replace it. -/
abbrev toggle : Dynamics where
  State := Bool
  EventAt := fun _ => Bool
  initial := false
  emit := id
  update := fun event => event

abbrev action : Law toggle ℤ where
  Generator := Unit
  rootExposureAt := fun occurrence => RootedAccountedUnfolding.zero occurrence
  rootExposure_root := fun _ => rfl
  seedAt := fun _ =>
    RootedAccountedUnfolding.zero (.relation (Finsupp.single () 1))
  continuationAt := fun _ =>
    RootedAccountedUnfolding.zero
      (fun _ => RootedAccountedUnfolding.zero
        (.relation (Finsupp.single () 1)))
  evaluatorAt := by
    intro state event
    change Bool at event
    exact RootedAccountedUnfolding.zero
      (fun _ : Unit => if event then (1 : ℤ) else 0)

theorem false_true_raw_evaluators :
    ((faithfulLaw action).rawAt
      ((eventPresentation toggle false).forward false)).evaluator.root () = 0 ∧
    ((faithfulLaw action).rawAt
      ((eventPresentation toggle false).forward true)).evaluator.root () = 1 := by
  exact ⟨rfl, rfl⟩

theorem false_true_raw_distinct :
    ((faithfulLaw action).rawAt
      ((eventPresentation toggle false).forward false)).evaluator ≠
    ((faithfulLaw action).rawAt
      ((eventPresentation toggle false).forward true)).evaluator := by
  intro same
  have values := congrArg
    (fun evaluator : RootedAccountedUnfolding (Unit → ℤ) =>
      evaluator.root ()) same
  change (0 : ℤ) = 1 at values
  omega

theorem same_current_receipts_distinct :
    receiptFromCompiler (D := toggle)
        ((eventPresentation toggle false).forward false) = false ∧
      receiptFromCompiler (D := toggle)
        ((eventPresentation toggle false).forward true) = true ∧
      (eventPresentation toggle false).forward true ≠
        (root toggle).emitted false := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have receiptSame := congrArg (receiptFromCompiler (D := toggle)) same
  change true = false at receiptSame
  cases receiptSame

theorem false_actual_equation :
    ((faithfulLaw action).faithfulAt (emitted toggle false)).freeEvaluation
      (Finsupp.single () 1) = 0 := by
  have generated := (generated_single_equation action false () 1).1
  have value : (action.evaluatorAt (toggle.emit false)).root () = (0 : ℤ) := rfl
  rw [value] at generated
  simpa only [one_smul] using generated

theorem true_actual_equation :
    ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () 1) = 1 := by
  have generated := (generated_single_equation action true () 1).1
  have value : (action.evaluatorAt (toggle.emit true)).root () = (1 : ℤ) := rfl
  rw [value] at generated
  simpa only [one_smul] using generated

theorem true_basis_relation_mem :
    Finsupp.single () (1 : ℤ) ∈
      ((faithfulLaw action).historyAt (emitted toggle true)).relationClosure := by
  let history := (faithfulLaw action).historyAt (emitted toggle true)
  apply history.relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (Finsupp.single () (1 : ℤ)) ∈
    history.observedEvents 0
  change PresentedRelationEventAt.relation (Finsupp.single () (1 : ℤ)) ∈
    [PresentedRelationEventAt.relation (Finsupp.single () (1 : ℤ))]
  simp

theorem true_not_relationsSound :
    ¬ ((faithfulLaw action).faithfulAt (emitted toggle true)).RelationsSound := by
  intro sound
  have killed := sound true_basis_relation_mem
  change ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
    (Finsupp.single () 1) = 0 at killed
  rw [true_actual_equation] at killed
  norm_num at killed

/-- The actual true receipt evaluates an installed relation to one, so the
classifier must return a nonzero relation residual at that same root event. -/
theorem true_event_installed_unsound :
    ∃ obstruction : GeneratedUnsoundRelationObstructionAt
        ((faithfulLaw action).faithfulAt (emitted toggle true)),
      ∃ coordinate : GeneratedRelationResidualCoordinateAt
          ((faithfulLaw action).faithfulAt (emitted toggle true)),
        (residualRoot action).source.projectionLaw.outcomeAt
          (.component PUnit.unit) ((residualRoot action).emitted true) =
            .inl ⟨PUnit.unit, .unsound obstruction coordinate⟩ ∧
        coordinate.coordinate ≠ 0 ∧
        HEq (((residualRoot action).toLedgerRoot.generatedLedgerAt true
            ).entryDisposition (entry toggle true))
          (LedgerEntryDispositionAt.evolved
            (LedgerEntryEvolutionAt.transferred true
              rfl rfl (Nat.le_refl _) :
                LedgerEntryEvolutionAt (network toggle)
                  (entry toggle true) (entry toggle true))) ∧
        ((residualRoot action).toRoot.evolutionAt true).nextCurrent? =
          some true := by
  generalize outcome_eq :
    ((faithfulLaw action).faithfulAt (emitted toggle true)).settleWithResidual =
      outcome
  cases outcome with
  | faithful soundness coverage realization =>
      exact False.elim (true_not_relationsSound soundness.sound)
  | unsound obstruction coordinate =>
      have generated := generated_event_ledger_next action true
      rw [outcome_eq] at generated
      exact ⟨obstruction, coordinate, generated.1,
        coordinate.coordinate_ne_zero, generated.2.1, generated.2.2⟩
  | kernelResidual soundness obstruction coordinate =>
      exact False.elim (true_not_relationsSound soundness.sound)
  | coverageResidual soundness obstruction coordinate =>
      exact False.elim (true_not_relationsSound soundness.sound)

theorem both_actual_events_accounted :
    ((residualRoot action).toRoot.evolutionAt false).nextCurrent? =
        some false ∧
      ((residualRoot action).toRoot.evolutionAt true).nextCurrent? =
        some true := by
  exact ⟨rfl, rfl⟩

#print axioms generated_single_equation
#print axioms generated_recovery_or_residual
#print axioms generated_event_ledger_next
#print axioms receiptFromCompiler_eq_event
#print axioms same_lower_root
#print axioms false_true_raw_distinct
#print axioms same_current_receipts_distinct
#print axioms false_actual_equation
#print axioms true_actual_equation
#print axioms true_event_installed_unsound
#print axioms both_actual_events_accounted

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
