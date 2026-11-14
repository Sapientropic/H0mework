import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionScalarPairingConsumer
import H0mework.Foundation.Source.TraceAdvance

/-!
# Nonzero scalar pairing from an actual generator-only source

Every finite observation contains only source generator events, so the
relation closure is zero. The actual evaluator reads one on its generated
class, giving a nonzero quotient pairing on the original receipt and row.
This separate law epoch is a positive control, not a replacement for the
unsound Boolean event.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalRelationGeneratedComplex

noncomputable section

/-! A second fixed source law controls the positive nonzero branch. Its
relation trace is empty because every generated event is a generator. -/

def generatorOnlyAction : Law toggle ℤ where
  Generator := Unit
  rootExposureAt := fun occurrence => RootedAccountedUnfolding.zero occurrence
  rootExposure_root := fun _ => rfl
  seedAt := fun _ => RootedAccountedUnfolding.zero (.generator ())
  continuationAt := fun _ =>
    RootedAccountedUnfolding.zero
      (fun _ => RootedAccountedUnfolding.zero (.generator ()))
  evaluatorAt := fun _ => RootedAccountedUnfolding.zero (fun _ => (1 : ℤ))

abbrev generatorHistory :=
  (historyLaw generatorOnlyAction).historyAt (emitted toggle true)

theorem generator_observation_only (stage : Nat) :
    ∀ event, event ∈ (generatorHistory.observation stage).trace →
      event = PresentedRelationEventAt.generator () := by
  induction stage with
  | zero =>
      intro event present
      change event ∈ [PresentedRelationEventAt.generator ()] at present
      exact List.mem_singleton.mp present
  | succ stage ih =>
      intro event present
      have priorOrNew := RootedAccountedUnfolding.trace_advance_cases
        generatorHistory.actualContinuation (generatorHistory.observation stage)
          event present
      rcases priorOrNew with old | ⟨_leaf, _frontier, fresh⟩
      · exact ih event old
      · change event ∈ [PresentedRelationEventAt.generator ()] at fresh
        exact List.mem_singleton.mp fresh

theorem generator_observed_only (stage : Nat) :
    ∀ event, event ∈ generatorHistory.observedEvents stage →
      event = PresentedRelationEventAt.generator () := by
  intro event present
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,
    List.mem_flatMap, List.mem_range] at present
  obtain ⟨index, _before, member⟩ := present
  exact generator_observation_only index event member

theorem generator_relationClosure_bot : generatorHistory.relationClosure = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    intro stage
    apply Submodule.span_le.mpr
    intro relation present
    have impossible := generator_observed_only stage
      (PresentedRelationEventAt.relation relation) present
    cases impossible
  · exact bot_le

theorem generator_is_supported : () ∈ generatorHistory.generatorSupport 0 := by
  classical
  letI : DecidableEq Unit := Classical.decEq Unit
  have root_event : PresentedRelationEventAt.generator () ∈
      generatorHistory.observedEvents 0 := by
    change PresentedRelationEventAt.generator () ∈ generatorHistory.seed.trace
    exact RootedAccountedUnfolding.root_mem_trace _
  apply List.mem_toFinset.mpr
  apply List.mem_flatMap.mpr
  refine ⟨.generator (), root_event, ?_⟩
  change () ∈ ({()} : Finset Unit).toList
  exact Finset.mem_toList.mpr (Finset.mem_singleton_self ())

theorem generator_single_in_closure :
    Finsupp.single () (1 : ℤ) ∈ generatorHistory.generatorClosure :=
  actual_generator_single_mem_closure generatorHistory 0 () generator_is_supported

theorem generator_relations_sound :
    ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)).RelationsSound := by
  intro relation present
  have zero : relation = 0 := by
    change relation ∈ generatorHistory.relationClosure at present
    rw [generator_relationClosure_bot] at present
    change relation ∈ (⊥ : Submodule ℤ
      ((faithfulLaw generatorOnlyAction).historyLaw.Generator →₀ ℤ)) at present
    exact (Submodule.mem_bot (R := ℤ)).1 present
  subst relation
  exact map_zero _

def generatorClass : generatorHistory.CompletionCarrier :=
  generatorHistory.completionProjection
    ⟨Finsupp.single () (1 : ℤ), generator_single_in_closure⟩

theorem generator_class_reads_one
    (soundness : GeneratedRelationSoundnessAt
      ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true))) :
    ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).completionEvaluation soundness generatorClass = 1 := by
  have equation := (generated_single_equation generatorOnlyAction true () 1).1
  have sourceValue :
      (generatorOnlyAction.evaluatorAt (toggle.emit true)).root () = (1 : ℤ) := rfl
  rw [sourceValue] at equation
  change ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
    ).freeEvaluation (Finsupp.single () 1) = 1
  simpa only [one_smul] using equation

theorem generator_pairing_from_receipt :
    ∃ soundness : GeneratedRelationSoundnessAt
        ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)),
      scalarPairing? generatorOnlyAction (emitted toggle true) =
        some (rankOnePairing
          (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
            ).completionEvaluation soundness)) := by
  have branch := (scalarPairing_source_branch generatorOnlyAction true).2.1
  generalize outcome_eq :
    ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).settleRelations = outcome at branch
  cases outcome with
  | sound soundness => exact ⟨soundness, branch.1⟩
  | unsound obstruction =>
      exact False.elim (obstruction.notSound generator_relations_sound)

/-- An actual nonzero source evaluator, with no relation events, generates
a nonzero quotient pairing. This is a distinct fixed law epoch used as a
positive control, not a replacement for the preceding true-event residual. -/
theorem generator_nonzero_pairing_original_row_next :
    ∃ soundness : GeneratedRelationSoundnessAt
        ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)),
      (scalarPairingRoot generatorOnlyAction).source.projectionLaw.outcomeAt
          (.component PUnit.unit)
          ((scalarPairingRoot generatorOnlyAction).emitted true) =
        .inl ⟨PUnit.unit, some (rankOnePairing
          (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
            ).completionEvaluation soundness))⟩ ∧
      rankOnePairing
        (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
          ).completionEvaluation soundness)
          generatorClass generatorClass = 1 ∧
      HEq (((scalarPairingRoot generatorOnlyAction).toLedgerRoot.generatedLedgerAt true
          ).entryDisposition (entry toggle true))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred true
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt (network toggle)
                (entry toggle true) (entry toggle true))) ∧
      ((scalarPairingRoot generatorOnlyAction).toRoot.evolutionAt true).nextCurrent? =
        some true := by
  obtain ⟨soundness, generated⟩ := generator_pairing_from_receipt
  refine ⟨soundness, ?_, ?_,
    (scalarPairing_inventory_ledger_next generatorOnlyAction true).2.1,
    (scalarPairing_inventory_ledger_next generatorOnlyAction true).2.2⟩
  · have installed := (scalarPairing_source_branch generatorOnlyAction true).1
    rw [generated] at installed
    exact installed
  · change (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).completionEvaluation soundness generatorClass) *
        (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
          ).completionEvaluation soundness generatorClass) = 1
    rw [generator_class_reads_one soundness]
    norm_num

#print axioms generator_nonzero_pairing_original_row_next

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
