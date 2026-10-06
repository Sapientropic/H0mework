import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
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
variable (queryWord : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord =
    nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count queryWord (current root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)).length=queryWord.length+3 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count queryWord)
abbrev pairExposure := SourceOperationPaidRelations.exposure
  (pairResult root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).2.1.2

theorem pair_inventory : (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).pairInventory=
    some (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) := rfl
theorem pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.model))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_same_execution : HEq (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)

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

theorem full_pair : (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).expression.eval
    (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).environment =
      (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord,
        SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) queryWord
          (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)-nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) := by
  change (SourceOperationScalarInventoryLift.liftExpr (programme root recognition visit successor transition alignment U7 calculus count queryWord)).eval
    (SourceOperationScalarInventoryLift.pairEnvironment
      (environmentAt root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord))
      (environmentAt root recognition visit successor transition alignment U7 calculus count (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)-
        environmentAt root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord)))=_
  rw [lift_difference,programme_value,programme_value]

namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
  (queryAt nextAt no_refill noetherian installed_born_inventory old_past_born)
end Request
theorem query_next (stage : Nat) : type_of% (Request.queryAt
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) ∧
    type_of% (Request.nextAt
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) :=
  ⟨Request.queryAt _ _ stage,Request.nextAt _ _ stage⟩
theorem same_debt (stage : Nat) : type_of% (Request.no_refill
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) ∧
    type_of% (Request.noetherian
      (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
      (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) stage) :=
  ⟨Request.no_refill _ _ stage,Request.noetherian _ _ stage⟩
theorem born_inventory : type_of% (Request.installed_born_inventory
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  Request.installed_born_inventory _ _
theorem all_inventory : type_of% (Request.old_past_born
    (seed root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
    (frame root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)) :=
  Request.old_past_born _ _
theorem original_read (following : List (Letter root recognition visit successor)) :
    readout root recognition visit successor transition alignment U7 calculus count following (normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)=
    read root recognition visit successor transition alignment U7 calculus count (SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count)
      ((seedWord++queryWord)++following) point) := by
  rw [normal_value]
  change readout root recognition visit successor transition alignment U7 calculus count following
    (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) queryWord
      (Inventory.normal root recognition visit successor transition alignment U7 calculus count point seedWord))=_
  rw [Inventory.normal_value,SourceGeneratedActionWords.run_source,SourceGeneratedActionWords.run_source,SourceGeneratedActionWords.readout_source]
  rw [SourceGeneratedActionWords.run_append,SourceGeneratedActionWords.run_append]
  rfl

theorem original_hilbert (bound : Nat) :
    observation root recognition visit successor transition alignment U7 calculus count bound (normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)=
      observation root recognition visit successor transition alignment U7 calculus count bound (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) :=
  congrArg (observation root recognition visit successor transition alignment U7 calculus count bound) (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)

theorem joint_material : ((component root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).project (.inl PUnit.unit)
    (root.emitted visit.current) PUnit.unit).2.2.2.2.2.2.2.2.1=
    acted root recognition visit successor transition alignment U7 calculus count point seedWord queryWord := rfl

theorem paid_recovery : recover root recognition visit successor transition alignment U7 calculus count (acted root recognition visit successor transition alignment U7 calculus count point seedWord queryWord).1=
    nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord := by
  exact (congrArg (recover root recognition visit successor transition alignment U7 calculus count) (acted_value root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)).trans
    ((recover_word root recognition visit successor transition alignment U7 calculus count queryWord (emit root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord))).trans
      (congrArg (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) queryWord)
        (recover_emit root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord))))

theorem original_future : sourceMap root recognition visit successor transition alignment U7 calculus count (recover root recognition visit successor transition alignment U7 calculus count (emit root recognition visit successor transition alignment U7 calculus count
      (normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))) = sourceMap root recognition visit successor transition alignment U7 calculus count (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord) := by
  exact congrArg (sourceMap root recognition visit successor transition alignment U7 calculus count)
    ((recover_emit root recognition visit successor transition alignment U7 calculus count (normal root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)).trans
      (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord queryWord))

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
