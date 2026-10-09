import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
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
variable (bound : Nat)
variable (queryWord : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord=
    effect root recognition visit successor transition alignment U7 calculus count bound queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count bound queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)).length=budget root recognition visit successor bound queryWord :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count bound queryWord)
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count bound)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)

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

theorem full_pair : (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).expression.eval
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).environment=
      (effect root recognition visit successor transition alignment U7 calculus count bound queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord),
        effect root recognition visit successor transition alignment U7 calculus count bound queryWord (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)-
          effect root recognition visit successor transition alignment U7 calculus count bound queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord)) := by
  change (SourceOperationScalarInventoryLift.liftExpr (programme root recognition visit successor transition alignment U7 calculus count bound queryWord)).eval
    (SourceOperationScalarInventoryLift.pairEnvironment
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound (current root recognition visit successor transition alignment U7 calculus count point seedWord))
      (environmentAt root recognition visit successor transition alignment U7 calculus count bound (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)-
        environmentAt root recognition visit successor transition alignment U7 calculus count bound (current root recognition visit successor transition alignment U7 calculus count point seedWord)))=_
  rw [lift_difference,programme_value,programme_value]

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)) :=
  Request.old_past_born _ _
theorem original_cell (cell : Cells root recognition visit successor bound) :
    normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord cell=
      NodeHilbert.Words.wordEvolution root recognition visit successor queryWord
        (NodeHilbert.measurement root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1)
            (current root recognition visit successor transition alignment U7 calculus count point seedWord))) cell.2-
      Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (queryWord++word root recognition visit successor cell.1)
          (current root recognition visit successor transition alignment U7 calculus count point seedWord)) :=
  (congrArg (fun values : Space root recognition visit successor bound => values cell)
    (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)).trans
    (effect_cell root recognition visit successor transition alignment U7 calculus count bound queryWord cell (current root recognition visit successor transition alignment U7 calculus count point seedWord))

abbrev branchNormal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord).toAuthoritativeRoot visit.current
  (branchReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
theorem branch_value : branchNormal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord=
    effect root recognition visit successor transition alignment U7 calculus count bound queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count bound queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))
theorem branch_effect : SourceGeneratedCovarianceExecution.EffectPredicate (Future.observation root recognition visit successor transition alignment U7 calculus count bound)
    (action root recognition visit successor transition alignment U7 calculus count bound queryWord) (selected root recognition visit successor transition alignment U7 calculus count bound queryWord)
      (branchNormal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) := by
  rw [branch_value]
  exact SourceGeneratedCovarianceExecution.source_effect_predicate _ _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
