import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects
open SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
open RootInquiryCompletion

theorem in_inventory (count : Nat) : relationWord root visit recognition ∈
    (combined root visit recognition count).relationClosure := by
  apply (combined root visit recognition count).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (relationWord root visit recognition) ∈
    (combined root visit recognition count).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ, List.range_zero,
    List.nil_append, List.flatMap_singleton, RootGeneratedCofinalHistoryAt.observation_zero]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 _ (seed root visit recognition count).root_mem_trace
def soundEvent := SourceOperationPaidRelations.soundEvent (sort:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition)

theorem seed_sound (count : Nat) :
    ∀ event ∈ (combinedSeed root visit recognition count).trace, soundEvent root visit recognition event := by
  intro event belongs
  change event ∈ PresentedRelationEventAt.relation (relationWord root visit recognition) ::
    ((seed root visit recognition count).trace ++
      ((SourceOperationPaidRelations.exposure (RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent
        (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)
          (paidRuntime root visit recognition count)).2).trace ++ [])) at belongs
  rcases List.mem_cons.mp belongs with equal | rest
  · exact equal ▸ generated_relation_zero root visit recognition
  · rcases List.mem_append.mp rest with left | right
    · change event ∈ [PresentedRelationEventAt.relation (relationWord root visit recognition)] at left
      have same := List.mem_singleton.mp left
      exact same ▸ generated_relation_zero root visit recognition
    · cases event with
      | generator _ => exact True.intro
      | relation word =>
          apply SourceOperationPaidRelations.exposure_sound _ word
          exact (List.mem_append.mp right).elim id (fun impossible => nomatch impossible)
theorem observation_sound (count stage : Nat) :
    ∀ event ∈ (combined root visit recognition count).observation stage |>.trace,
      soundEvent root visit recognition event := by
  induction stage with
  | zero => exact seed_sound root visit recognition count
  | succ stage previous => exact SourceOperationPaidRelations.advance_preserves _ _ previous
theorem word_read (count : Nat) (word : Word root visit recognition) :
    (face root visit recognition count).freeEvaluation word =
      SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition) word := by
  classical
  induction word using Finsupp.induction with
  | zero => exact (face root visit recognition count).freeEvaluation.map_zero
  | @single_add expression integer rest absent nonzero previous =>
      calc
        (face root visit recognition count).freeEvaluation (Finsupp.single expression integer + rest) =
            (face root visit recognition count).freeEvaluation (Finsupp.single expression integer) +
              (face root visit recognition count).freeEvaluation rest :=
          (face root visit recognition count).freeEvaluation.map_add _ _
        _ = integer • expression.eval (mixed root visit recognition) +
            SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition) rest :=
          congrArg₂ (· + ·)
            (CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single
              (face root visit recognition count) expression integer) previous
        _ = SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
            (mixed root visit recognition) (Finsupp.single expression integer + rest) := by
          rw [map_add, Finsupp.linearCombination_single]

theorem relations_sound (count : Nat) : (face root visit recognition count).RelationsSound := by
  apply iSup_le
  intro stage
  apply Submodule.span_le.mpr
  intro word belongs
  change (face root visit recognition count).freeEvaluation word = 0
  apply (word_read root visit recognition count word).trans
  change PresentedRelationEventAt.relation word ∈ (combined root visit recognition count).observedEvents stage at belongs
  rw [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap] at belongs
  obtain ⟨index,_,eventMem⟩ := belongs
  exact observation_sound root visit recognition count index _ eventMem
theorem paid_step_in_inventory (count : Nat) (word : Word root visit recognition)
    (belongs : word ∈ SourceOperationPaidRelations.words (RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent
      (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)
        (paidRuntime root visit recognition count)).2) :
    word ∈ (combined root visit recognition count).relationClosure := by
  apply (combined root visit recognition count).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation word ∈ (combined root visit recognition count).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ, List.range_zero,
    List.nil_append, List.flatMap_singleton, RootGeneratedCofinalHistoryAt.observation_zero]
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  apply List.mem_cons_of_mem
  exact Eq.mpr (congrArg (fun events => PresentedRelationEventAt.relation word ∈ events)
      (SourceOperationPaidRelations.events_trace (RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent
        (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)
          (paidRuntime root visit recognition count)).2)) (List.mem_map.mpr ⟨word,belongs,rfl⟩)

theorem seed_material (count : Nat) : seed root visit recognition count = incomingSeed root visit recognition := rfl

theorem source_factorizes (count : Nat) : type_of%
    ((RootGeneratedDebtActivationJointSource.OwnerFree.facade (actualRoot root visit recognition).toAuthoritativeRoot
      visit.current (installedReader root visit recognition)).readoutAt_factorizes
      (paidRuntime root visit recognition count) (sourceFace root visit recognition count).projection) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.facade (actualRoot root visit recognition).toAuthoritativeRoot
    visit.current (installedReader root visit recognition)).readoutAt_factorizes
    (paidRuntime root visit recognition count) (sourceFace root visit recognition count).projection

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
