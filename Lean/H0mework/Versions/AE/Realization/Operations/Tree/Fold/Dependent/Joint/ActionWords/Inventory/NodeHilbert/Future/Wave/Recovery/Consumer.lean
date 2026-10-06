import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

variable (point : Carrier root recognition visit successor)
variable (seedWord : List (Letter root recognition visit successor))
variable (historyWord : List (Letter root recognition visit successor))
variable (queryWord : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord =
    nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)).length=queryWord.length+3 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count queryWord)
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.model))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)

private theorem lift_difference {Sorts : Type u} {Values Variables : Sorts → Type u}
    [∀ target, AddCommGroup (Values target)] {target : Sorts}
    (expression : Expr Values Variables target) (before after : Env Values Variables) :
    (SourceOperationScalarInventoryLift.liftExpr expression).eval
      (SourceOperationScalarInventoryLift.pairEnvironment before (after-before)) =
      (expression.eval before,expression.eval after-expression.eval before) := by
  rw [SourceOperationScalarInventoryLift.eval_liftExpr]
  apply Prod.ext
  · rfl
  · have square := Expr.eval_update expression before (after-before)
    rw [add_sub_cancel] at square
    exact eq_sub_of_add_eq (by rw [add_comm]; exact square.symm)

theorem full_pair : (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).expression.eval
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).environment =
      (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord,
        SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count) queryWord
          (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)-nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) := by
  have paired := lift_difference (programme root recognition visit successor transition alignment U7 calculus count queryWord)
    (environmentAt root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))
    (environmentAt root recognition visit successor transition alignment U7 calculus count (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))
  exact paired.trans (congrArg₂ Prod.mk
    (programme_value root recognition visit successor transition alignment U7 calculus count queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))
    (congrArg₂ (· - ·)
      (programme_value root recognition visit successor transition alignment U7 calculus count queryWord (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))
      (programme_value root recognition visit successor transition alignment U7 calculus count queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))))

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)) :=
  Request.old_past_born _ _
theorem joint_material : ((component root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).project (.inl PUnit.unit)
    (root.emitted visit.current) PUnit.unit).2.2.2.2.2.2.2.2.1=
    acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord := rfl

theorem paid_recovery : recover root recognition visit successor transition alignment U7 calculus count (acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).1=
    nextValue root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord := by
  exact (congrArg (recover root recognition visit successor transition alignment U7 calculus count) (acted_value root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)).trans
    ((recover_word root recognition visit successor transition alignment U7 calculus count queryWord (emit root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))).trans
      (congrArg (SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count) queryWord)
        (recover_emit root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))))

abbrev sourceExposure := SourceOperationPaidRelations.exposure
  (sourceResult root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).2.1.2
theorem source_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).inventory=
    some (sourceExposure root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) := rfl
theorem source_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (Value root recognition visit successor transition alignment U7 calculus count) Var Slot.model))
    (present : event ∈ (sourceExposure root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.updatedSeed
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))).trace :=
  PaidSourceOrbit.SourceInventoryReceipt.consumed _ _ _
    (source_inventory root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord) event present
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
