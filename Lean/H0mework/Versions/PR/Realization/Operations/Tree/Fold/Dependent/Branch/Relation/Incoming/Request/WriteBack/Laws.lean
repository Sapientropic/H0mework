import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
variable (coordinate : GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem actual_seed_read (stage : Nat) :
    (historyFace root visit recognition count sound coordinate U7 calculus stage).rootRead.1 =
      updatedSeed root visit recognition count sound coordinate := rfl

theorem actual_action_read (stage : Nat) :
    (historyFace root visit recognition count sound coordinate U7 calculus stage).rootRead.2 =
      SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Action.material root visit recognition := rfl

theorem actual_word_in_inventory (stage : Nat) : word root visit recognition count sound coordinate ∈
    (actualUpdated root visit recognition count sound coordinate stage).relationClosure := by
  apply (actualUpdated root visit recognition count sound coordinate stage).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (word root visit recognition count sound coordinate) ∈
    (actualUpdated root visit recognition count sound coordinate stage).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
    List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_right _ _ _).1 _ (event root visit recognition count sound coordinate).root_mem_trace

theorem prior_seed_preserved (stage : Nat) : ∀ atom ∈ (combinedSeed root visit recognition count).trace,
    atom ∈ (actualSeed root visit recognition count sound coordinate stage).trace := by
  intro atom belongs
  exact (SourceHistoryCommon.parallel_left _ _ _).1 _
    ((SourceHistoryCommon.parallel_left _ _ _).1 _ belongs)

def actualTransition (stage : Nat) : CofinalHistoryTransition.GeneratedTransition (combined root visit recognition count)
    (actualUpdated root visit recognition count sound coordinate stage) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _
      (prior_seed_preserved root visit recognition count sound coordinate stage)) (by
      intro direction belongs
      change (actualUpdated root visit recognition count sound coordinate stage).completionProjection
        ⟨direction.val,SourceOperationPaidRelations.generators_next _ _ _ _
          (prior_seed_preserved root visit recognition count sound coordinate stage) direction.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _
        (prior_seed_preserved root visit recognition count sound coordinate stage) belongs)

theorem actual_coordinate_paid (stage : Nat) :
    CofinalHistoryTransition.GeneratedTransition.completionMap (combined root visit recognition count)
      (actualUpdated root visit recognition count sound coordinate stage)
      (actualTransition root visit recognition count sound coordinate stage) coordinate.coordinate.val = 0 := by
  rw [← kernel_word_read root visit recognition count sound coordinate]
  apply (SourceHistoryCommon.transition_fibre_zero _ _ _ _).mpr
  exact actual_word_in_inventory root visit recognition count sound coordinate stage
theorem actual_seed_sound (stage : Nat) :
    ∀ atom ∈ (actualSeed root visit recognition count sound coordinate stage).trace,
      SourceOperationPaidRelations.soundEvent (sort:=SourceOperationNative.Tree.Fold.Slot.result)
        (mixed root visit recognition) atom := by
  intro atom belongs
  change atom ∈ (updatedSeed root visit recognition count sound coordinate).root ::
    ((updatedSeed root visit recognition count sound coordinate).trace ++
      ((RootGeneratedDebtActivationJointSource.OwnerFree.Relations.exposure
        (sourceRoot root visit recognition count sound coordinate).toAuthoritativeRoot
        (sourceVisit root visit recognition count sound coordinate).current
        (requestReader root visit recognition count (word root visit recognition count sound coordinate))
        (actualRuntime root visit recognition count sound coordinate stage)).trace ++ [])) at belongs
  rcases List.mem_cons.mp belongs with same | rest
  · exact same ▸ seed_sound root visit recognition count _ (combinedSeed root visit recognition count).root_mem_trace
  · rcases List.mem_append.mp rest with prior | paid
    · change atom ∈ (combinedSeed root visit recognition count).root ::
        ((combinedSeed root visit recognition count).trace ++
          ((event root visit recognition count sound coordinate).trace ++ [])) at prior
      rcases List.mem_cons.mp prior with same | rest
      · exact same ▸ seed_sound root visit recognition count _ (combinedSeed root visit recognition count).root_mem_trace
      · rcases List.mem_append.mp rest with old | new
        · exact seed_sound root visit recognition count _ old
        · have eventMem := (List.mem_append.mp new).elim id (fun impossible => nomatch impossible)
          change atom ∈ [PresentedRelationEventAt.relation (word root visit recognition count sound coordinate)] at eventMem
          have same := List.mem_singleton.mp eventMem
          exact same ▸ kernel_word_value root visit recognition count sound coordinate
    · cases atom with
      | generator _ => exact True.intro
      | relation relationWord =>
          apply SourceOperationPaidRelations.exposure_sound _ relationWord
          exact (List.mem_append.mp paid).elim id (fun impossible => nomatch impossible)

theorem actual_word_read (stage : Nat) (relationWord : Word root visit recognition) :
    (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation relationWord =
      SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
        (mixed root visit recognition) relationWord := by
  classical
  induction relationWord using Finsupp.induction with
  | zero => exact (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation.map_zero
  | @single_add expression integer rest absent nonzero previous =>
      calc
        (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation (Finsupp.single expression integer + rest) =
            (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation (Finsupp.single expression integer) +
              (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation rest :=
          (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation.map_add _ _
        _ = integer • expression.eval (mixed root visit recognition) +
            SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
              (mixed root visit recognition) rest :=
          congrArg₂ (· + ·)
            (CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single
              (evaluationFace root visit recognition count sound coordinate stage) expression integer) previous
        _ = SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
            (mixed root visit recognition) (Finsupp.single expression integer + rest) := by
          rw [map_add, Finsupp.linearCombination_single]

theorem actual_observation_sound (stage observation : Nat) :
    ∀ atom ∈ (actualUpdated root visit recognition count sound coordinate stage).observation observation |>.trace,
      SourceOperationPaidRelations.soundEvent (sort:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition) atom := by
  induction observation with
  | zero => exact actual_seed_sound root visit recognition count sound coordinate stage
  | succ observation previous => exact SourceOperationPaidRelations.advance_preserves _ _ previous

theorem actual_relations_sound (stage : Nat) :
    (evaluationFace root visit recognition count sound coordinate stage).RelationsSound := by
  apply iSup_le
  intro observation
  apply Submodule.span_le.mpr
  intro relationWord belongs
  change (evaluationFace root visit recognition count sound coordinate stage).freeEvaluation relationWord = 0
  apply (actual_word_read root visit recognition count sound coordinate stage relationWord).trans
  change PresentedRelationEventAt.relation relationWord ∈
    (actualUpdated root visit recognition count sound coordinate stage).observedEvents observation at belongs
  rw [RootGeneratedCofinalHistoryAt.observedEvents,List.mem_flatMap] at belongs
  obtain ⟨index,_,member⟩ := belongs
  exact actual_observation_sound root visit recognition count sound coordinate stage index _ member
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
