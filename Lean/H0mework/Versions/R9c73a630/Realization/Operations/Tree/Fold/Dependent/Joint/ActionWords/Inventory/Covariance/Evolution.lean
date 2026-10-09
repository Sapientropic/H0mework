import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
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
variable (actor : Actor root recognition visit successor)
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
open SourceOperationScalarInventoryLift
def sourceFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Inventory.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).source.base
    (component root recognition visit successor transition alignment U7 calculus count actor point word)).embed (.inl PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl
abbrev nextValue := ((sourceFace root recognition visit successor transition alignment U7 calculus count actor point word).rootRead.2.2.1).integralTransition
  ((sourceFace root recognition visit successor transition alignment U7 calculus count actor point word).rootRead.2.2.2.1)
def nextRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=Slot.measured) :=
  ⟨environmentAt root recognition visit successor transition alignment U7 calculus count
      (nextValue root recognition visit successor transition alignment U7 calculus count actor point word),
    programme root recognition visit successor transition alignment U7 calculus count actor⟩
theorem next_environment : (nextRaw root recognition visit successor transition alignment U7 calculus count actor point word).environment =
    updatedEnvironment root recognition visit successor transition alignment U7 calculus count actor point word := rfl

theorem frame_environment {current : (frame root recognition visit successor transition alignment U7 calculus count actor point word).V.Current}
    (occurrence : (frame root recognition visit successor transition alignment U7 calculus count actor point word).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (frame root recognition visit successor transition alignment U7 calculus count actor point word).environment occurrence =
      (nextRaw root recognition visit successor transition alignment U7 calculus count actor point word).environment := rfl

def pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PairValue (Value root recognition visit successor transition alignment U7 calculus count)) (Var:=Var) (sort:=Slot.measured) :=
  ⟨pairEnvironment (raw root recognition visit successor transition alignment U7 calculus count actor point word).environment
      ((nextRaw root recognition visit successor transition alignment U7 calculus count actor point word).environment-
        (raw root recognition visit successor transition alignment U7 calculus count actor point word).environment),
    liftExpr (raw root recognition visit successor transition alignment U7 calculus count actor point word).expression⟩

private theorem lift_difference {Sorts : Type u} {Values Variables : Sorts → Type u}
    [∀ target, AddCommGroup (Values target)] {target : Sorts}
    (expression : Expr Values Variables target) (before after : Env Values Variables) :
    (liftExpr expression).eval (pairEnvironment before (after-before)) =
      (expression.eval before,expression.eval after-expression.eval before) := by
  rw [eval_liftExpr]
  apply Prod.ext
  · rfl
  · have square := Expr.eval_update expression before (after-before)
    rw [add_sub_cancel] at square
    exact eq_sub_of_add_eq (by rw [add_comm]; exact square.symm)

theorem full_pair : (pairRaw root recognition visit successor transition alignment U7 calculus count actor point word).expression.eval
    (pairRaw root recognition visit successor transition alignment U7 calculus count actor point word).environment =
      (effect root recognition visit successor transition alignment U7 calculus count actor
          (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word),
        effect root recognition visit successor transition alignment U7 calculus count actor
            (nextValue root recognition visit successor transition alignment U7 calculus count actor point word) -
          effect root recognition visit successor transition alignment U7 calculus count actor
            (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)) := by
  change (liftExpr (programme root recognition visit successor transition alignment U7 calculus count actor)).eval
    (pairEnvironment (environment root recognition visit successor transition alignment U7 calculus count point word)
      (updatedEnvironment root recognition visit successor transition alignment U7 calculus count actor point word-
        environment root recognition visit successor transition alignment U7 calculus count point word)) = _
  rw [lift_difference,programme_value,programme_next]
  rfl

def pairFace : SourceNativeRootSemanticFaceAt
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word) visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (Inventory.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).source.base
    (component root recognition visit successor transition alignment U7 calculus count actor point word)).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def pairReader (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((component root recognition visit successor transition alignment U7 calculus count actor point word).project (.inr PUnit.unit) occurrence PUnit.unit).1
abbrev pairRuntime := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime
  (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word) visit U7 calculus
  (pairReader root recognition visit successor transition alignment U7 calculus count actor point word)

theorem pair_source : (pairFace root recognition visit successor transition alignment U7 calculus count actor point word).rootRead.1 =
    pairRaw root recognition visit successor transition alignment U7 calculus count actor point word := rfl

theorem pair_same_execution : HEq
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
      (pairReader root recognition visit successor transition alignment U7 calculus count actor point word))
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (Inventory.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot visit.current
      (pairSourceReader root recognition visit successor transition alignment U7 calculus count actor point word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _
    (pairSourceRaw root recognition visit successor transition alignment U7 calculus count actor point word)

theorem pair_normal : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count actor point word) =
      (effect root recognition visit successor transition alignment U7 calculus count actor
          (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word),
        effect root recognition visit successor transition alignment U7 calculus count actor
            (nextValue root recognition visit successor transition alignment U7 calculus count actor point word) -
          effect root recognition visit successor transition alignment U7 calculus count actor
            (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (full_pair root recognition visit successor transition alignment U7 calculus count actor point word)

theorem initial_pair_inventory :
    (frame root recognition visit successor transition alignment U7 calculus count actor point word).pairInventory =
      some (pairExposure root recognition visit successor transition alignment U7 calculus count actor point word) := rfl

theorem initial_pair_consumed (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count actor point word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count actor point word)
      (frame root recognition visit successor transition alignment U7 calculus count actor point word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (frame root recognition visit successor transition alignment U7 calculus count actor point word))).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem initial_pair_born (event : CofinalHistorySettlement.PresentedRelationEventAt
      (Expr (PairValue (Value root recognition visit successor transition alignment U7 calculus count)) Var Slot.measured))
    (present : event ∈ (pairExposure root recognition visit successor transition alignment U7 calculus count actor point word).trace) :
    event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
      (seed root recognition visit successor transition alignment U7 calculus count actor point word)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch
        (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.born (seed root recognition visit successor transition alignment U7 calculus count actor point word)
          (frame root recognition visit successor transition alignment U7 calculus count actor point word)))
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
        (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.born (seed root recognition visit successor transition alignment U7 calculus count actor point word)
          (frame root recognition visit successor transition alignment U7 calculus count actor point word)))).trace := by
  apply Request.old_past_born _ _ event
  apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.current_written_preserved _ _ event
  apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves _ _ _ event
  exact initial_pair_consumed root recognition visit successor transition alignment U7 calculus count actor point word event present

theorem pair_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count actor point word)).length = 7 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans (by rfl)

theorem pair_whole_next (stage : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (sourceRoot root recognition visit successor transition alignment U7 calculus count actor point word).toAuthoritativeRoot visit.current
    (pairReader root recognition visit successor transition alignment U7 calculus count actor point word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next _ _ _ stage

abbrev generatedEvolution := (generated root recognition visit successor transition alignment U7 calculus count actor point word,
  pairRuntime root recognition visit successor transition alignment U7 calculus count actor point word)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
