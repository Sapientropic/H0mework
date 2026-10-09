import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Intake
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Math
variable {S : Type u} {A X : S → Type u} [∀ s,AddCommGroup (A s)] {s : S}
theorem lift_fee (expr : Expr A X s) : remaining (liftExpr expr)=remaining expr := by
 induction expr with
 | var => rfl
 | const => rfl
 | add _ _ a b => exact congrArg₂ (fun a b : Nat => a+b+1) a b
 | linear _ _ a => exact congrArg (fun a : Nat => a+1) a
 | bilinear _ _ _ a b => exact congrArg₂ (fun a b : Nat => a+b+1) a b
theorem right_lift_fee (expr : Expr A X s) : remaining (P.L.right (liftExpr expr))=remaining expr :=
 (JointLow.right_charge _).trans (lift_fee _)
theorem right_lift_value (expr : Expr A X s) (first : Env (PairValue A) X) (old increment : Env A X) :
 (P.L.right (liftExpr expr)).eval (JointLow.environment first (pairEnvironment old increment))=
 (expr.eval old,expr.effect old increment) := (JointLow.right_value _ _ _).trans (eval_liftExpr _ _ _)
theorem append_recovered (first second : Expr A X s) (env : Env A X) :
 (Expr.add first second).eval env-second.eval env=first.eval env := add_sub_cancel_right _ _
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (oldRoot : SourceNativeAuthoritativeRootClosure N V)
variable (input : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=A) (Var:=X) (sort:=s))
variable (term : Expr A X s) {current : V.Current}
variable (occurrence : oldRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)
def appended : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=A) (Var:=X) (sort:=s) :=
 ⟨input.environment,.add input.expression term⟩
theorem source_value : (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt oldRoot
 (fun {_current} _ => appended input term) occurrence).2.2.1=input.expression.eval input.environment+term.eval input.environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem source_recovered : (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt oldRoot
 (fun {_current} _ => appended input term) occurrence).2.2.1-term.eval input.environment=input.expression.eval input.environment := by
 rw [source_value,add_sub_cancel_right]
end Math
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
local instance : ∀ s,AddCommGroup (Value root visit recognition s) := inferInstance
local instance : AddCommGroup (Value root visit recognition (slot root recognition)) :=
 CurrentChild.instAddCommGroupValue root visit recognition (slot root recognition)
namespace Lower
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem raw_fee : remaining (raw root visit recognition U7 calculus anchor sourceStage frame supplied).expression=
 remaining (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression+
 remaining frame.registered.input.expression+1 := by
 change remaining (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression+
  remaining (debtTerm root visit recognition frame)+1=_
 rw [debtTerm,Math.right_lift_fee]
 rfl
theorem debt_value (first : Env (PairValue (Value root visit recognition)) (Variable root visit recognition))
 (old increment : Env (Value root visit recognition) (Variable root visit recognition)) : type_of%
 (Math.right_lift_value frame.rawRead.expression first old increment) := Math.right_lift_value _ _ _ _
theorem helper_value : type_of% (Math.source_value (A.Shared.base frame).root.toAuthoritativeRoot
 (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied)
 (debtTerm root visit recognition frame) supplied) := Math.source_value _ _ _ _
theorem helper_recovered : type_of% (Math.source_recovered (A.Shared.base frame).root.toAuthoritativeRoot
 (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied)
 (debtTerm root visit recognition frame) supplied) := Math.source_recovered _ _ _ _
theorem paid_value : (paid root visit recognition U7 calculus anchor sourceStage frame supplied).2.2.1=
 (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression.eval
  (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).environment+
 (debtTerm root visit recognition frame).eval
  (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).environment :=
 helper_value root visit recognition U7 calculus anchor sourceStage frame supplied
theorem previous_recovered : (paid root visit recognition U7 calculus anchor sourceStage frame supplied).2.2.1-
 (debtTerm root visit recognition frame).eval
  (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).environment=
 (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression.eval
  (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).environment :=
 by
  rw [paid_value root visit recognition U7 calculus anchor sourceStage frame supplied]
  exact add_sub_cancel_right _ _
theorem trace_fee : (trace root visit recognition U7 calculus anchor sourceStage frame supplied).length=
 remaining (originalRaw root visit recognition U7 calculus anchor sourceStage frame supplied).expression+
 remaining frame.registered.input.expression+1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
 (raw_fee root visit recognition U7 calculus anchor sourceStage frame supplied)
abbrev actualResult := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultAt frame
 (configuration root visit recognition U7 calculus anchor sourceStage) supplied
theorem result_value : (actualResult root visit recognition U7 calculus anchor sourceStage frame supplied).2.2.1=
 (paid root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied).2.2.1 := by
 exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame
   (configuration root visit recognition U7 calculus anchor sourceStage)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame
   (configuration root visit recognition U7 calculus anchor sourceStage)).reader supplied).trans
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (A.Shared.base (A.epoch frame)).root.toAuthoritativeRoot
   (fun {_current} occurrence => raw root visit recognition U7 calculus anchor sourceStage (A.epoch frame) occurrence)
   supplied).symm
theorem result_trace : HEq (actualResult root visit recognition U7 calculus anchor sourceStage frame supplied).2.1.2
 (trace root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied) := by
 change HEq
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame
    (configuration root visit recognition U7 calculus anchor sourceStage)).toAuthoritativeRoot current
   (fun _ => raw root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied))
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (A.Shared.base (A.epoch frame)).root.toAuthoritativeRoot current
   (fun _ => raw root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied))
 exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _ _
theorem result_exposure : SourceOperationPaidRelations.exposure
 (actualResult root visit recognition U7 calculus anchor sourceStage frame supplied).2.1.2=
 SourceOperationPaidRelations.exposure (trace root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied) := by
 change SourceOperationPaidRelations.exposure
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame
    (configuration root visit recognition U7 calculus anchor sourceStage)).toAuthoritativeRoot current
   (fun _ => raw root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied))=
 SourceOperationPaidRelations.exposure
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (A.Shared.base (A.epoch frame)).root.toAuthoritativeRoot current
   (fun _ => raw root visit recognition U7 calculus anchor sourceStage (A.epoch frame) supplied))
 exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure _ _ _ _ _
end Lower
variable (stage : Nat)
theorem receiver_strict : remaining (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression<
 remaining (receiver root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression := by
 have budget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget
  (sourceMaterial root visit recognition U7 calculus anchor sourceStage stage)
 change remaining (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression<
 remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
  (sourceMaterial root visit recognition U7 calculus anchor sourceStage stage))
 rw [budget]
 have fee := Lower.raw_fee root visit recognition U7 calculus anchor sourceStage
  (A.epoch (sourceFrame root visit recognition U7 calculus anchor sourceStage stage))
  (SourceGeneratedInquiryReceiptAction.occurrence
   (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage))
 change remaining (sourceMaterial root visit recognition U7 calculus anchor sourceStage stage).raw=
  remaining (Lower.originalRaw root visit recognition U7 calculus anchor sourceStage
   (A.epoch (sourceFrame root visit recognition U7 calculus anchor sourceStage stage))
   (supplied root visit recognition U7 calculus anchor sourceStage stage)).expression+
  remaining (sourceFrame root visit recognition U7 calculus anchor sourceStage stage).registered.input.expression+1 at fee
 rw [fee]
 omega

theorem target_root (event : Event root visit recognition U7 calculus anchor sourceStage stage) :
 (targetAt root visit recognition U7 calculus anchor sourceStage stage event).targetRoot=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root
  (receiver root visit recognition U7 calculus anchor sourceStage stage)
  (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage) := rfl
theorem target_next (event : Event root visit recognition U7 calculus anchor sourceStage stage) :
 (targetAt root visit recognition U7 calculus anchor sourceStage stage event).targetAnswerAndNext.nextCurrent=
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (receiver root visit recognition U7 calculus anchor sourceStage stage).registered
  (receiver root visit recognition U7 calculus anchor sourceStage stage).packetAt,
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root
  (receiver root visit recognition U7 calculus anchor sourceStage stage)
  (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)).toAuthoritativeRoot,
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit
  (receiver root visit recognition U7 calculus anchor sourceStage stage)
  (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)⟩ := by
 change (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root
  (receiver root visit recognition U7 calculus anchor sourceStage stage)
  (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)).generatedNextCurrentAt
  (.finite (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root
   (receiver root visit recognition U7 calculus anchor sourceStage stage)
   (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage)).toAuthoritativeRoot.toRoot.initialVisit)=_
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl
theorem compiles : (state root visit recognition U7 calculus anchor sourceStage stage).compileInquiry
 (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage))=
 .debtAdmission (generatedAction root visit recognition U7 calculus anchor sourceStage stage) := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus anchor sourceStage stage).initialState.engine.node=
 .active (targetPresentation root visit recognition U7 calculus anchor sourceStage stage) := rfl
theorem whole_first (event : Event root visit recognition U7 calculus anchor sourceStage stage) : type_of%
 (targetAt root visit recognition U7 calculus anchor sourceStage stage event).firstDestination_heq :=
 (targetAt root visit recognition U7 calculus anchor sourceStage stage event).firstDestination_heq
theorem old_outcome (event : Event root visit recognition U7 calculus anchor sourceStage stage)
 (projection : (old root visit recognition U7 calculus anchor sourceStage stage).root.toAuthoritativeRoot.source.projectionLaw.Projection) : type_of%
 ((targetAt root visit recognition U7 calculus anchor sourceStage stage event).oldOutcome_heq projection) :=
 (targetAt root visit recognition U7 calculus anchor sourceStage stage event).oldOutcome_heq projection
theorem actual_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next
 (receiver root visit recognition U7 calculus anchor sourceStage stage)
 (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage) offset) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next _ _ _
theorem actual_query (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query
 (receiver root visit recognition U7 calculus anchor sourceStage stage)
 (receiverConfiguration root visit recognition U7 calculus anchor sourceStage stage) offset) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query _ _ _
theorem source_effect : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value
 (R:=ℤ) (sourceMaterial root visit recognition U7 calculus anchor sourceStage stage)) :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value _
theorem successor_valid : (targetPresentation root visit recognition U7 calculus anchor sourceStage stage).erase=
 (RootInquiryProcessNode.answered (sourcePresentation root visit recognition U7 calculus anchor sourceStage stage)
  (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage))).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation root visit recognition U7 calculus anchor sourceStage stage)).PreservesGeneratedLivingLawAt
  (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage))
  (.active (targetPresentation root visit recognition U7 calculus anchor sourceStage stage)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid
  (sourcePresentation root visit recognition U7 calculus anchor sourceStage stage)
  (targetPresentation root visit recognition U7 calculus anchor sourceStage stage)
  (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage))
  (generatedAction root visit recognition U7 calculus anchor sourceStage stage)
  (compiles root visit recognition U7 calculus anchor sourceStage stage)
 · exact (congrArg (fun current =>
   (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
    (receiver root visit recognition U7 calculus anchor sourceStage stage).registered,current⟩ : AnyAuthoritativeRootCurrent.{u}))
   (target_next root visit recognition U7 calculus anchor sourceStage stage
    (SourceGeneratedInquiryReceiptAction.sourceEvent
     (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
     (configuration root visit recognition U7 calculus anchor sourceStage)))).symm
 · exact HEq.rfl
theorem runtime_source_gate : ((runtime root visit recognition U7 calculus anchor sourceStage stage).initialState.engine.node).erase=
 (RootInquiryProcessNode.answered (sourcePresentation root visit recognition U7 calculus anchor sourceStage stage)
  (A.Shared.query (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
   (configuration root visit recognition U7 calculus anchor sourceStage))).erase := by
 rw [actual_initial]
 exact (successor_valid root visit recognition U7 calculus anchor sourceStage stage).1
theorem scalar_preserved (event) (present : event ∈ (originalScalar root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (scalarStock root visit recognition U7 calculus anchor sourceStage stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem pair_preserved (event) (present : event ∈ (originalPair root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (pairStock root visit recognition U7 calculus anchor sourceStage stage).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem main_trace_preserved (event) (present : event ∈
 (SourceGeneratedInquiryReceiptAction.Configured.lowStock
  (sourceFrame root visit recognition U7 calculus anchor sourceStage stage)
  (configuration root visit recognition U7 calculus anchor sourceStage)).trace) :
 event ∈ (scalarStock root visit recognition U7 calculus anchor sourceStage stage).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event
  (SourceGeneratedInquiryReceiptAction.Configured.main_event_preserved _ _ event present)
theorem scalar_seed_preserved (event) (present : event ∈ (scalarStock root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (seed root visit recognition U7 calculus anchor sourceStage stage).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
