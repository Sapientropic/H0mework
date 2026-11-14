import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock
import H0mework.Foundation.Responsibility.JointSource.Progress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.JointMeasuredProgramme
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.JointMeasured
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

omit [InnerProductSpace ℂ K] in
theorem embed_eval {sort : OldSlot} (term : Expr OldValue OldVar sort) (environment : Env (Value K) Var) :
    (embed term).eval environment = term.eval (oldEnvironment environment) := by
  induction term with
  | var name => rfl
  | const value => rfl
  | add first second ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | linear operation argument ih => exact congrArg operation ih
  | bilinear operation first second ih₁ ih₂ => exact congrArg₂ (fun x y => operation x y) ih₁ ih₂

omit [InnerProductSpace ℂ K] in
theorem output_embed_eval (term : Expr OldValue OldVar PaidSourceMacroHistory.Slot.orbit)
    (environment : Env (Value K) Var) :
    (outputEmbed term).eval environment = (term.eval (oldEnvironment environment),0) := by
  change oldInjection ((embed term).eval environment) = _
  rw [embed_eval]
  rfl
theorem seed_expression_value {ι : Type*} [Fintype ι] [DecidableEq ι] (source : ι → K)
    (environment : Env (Value K) Var) :
    (seedExpression source).eval environment =
      (PaidSourceMacroHistory.programme.eval (oldEnvironment environment),
        FG.innovationCLM source (environment Slot.measured PUnit.unit)) := by
  change (outputEmbed PaidSourceMacroHistory.programme).eval environment +
    measuredInjection (FG.innovationCLM source (environment Slot.measured PUnit.unit)) = _
  rw [output_embed_eval]
  apply Prod.ext
  · exact add_zero _
  · exact zero_add _
omit [InnerProductSpace ℂ K] in
theorem old_increment_value (read : Orbit →ₗ[ℤ] K) (environment : Env (Value K) Var) :
    (oldIncrementTerm read).eval environment =
      read (PaidSourceMacroHistory.programme.eval (oldEnvironment environment) -
        oldEnvironment environment PaidSourceMacroHistory.Slot.orbit PUnit.unit) := by
  change read ((embed PaidSourceMacroHistory.programme).eval environment +
    -(environment (.old PaidSourceMacroHistory.Slot.orbit) PUnit.unit)) = _
  rw [embed_eval]
  simp only [sub_eq_add_neg,oldEnvironment]
omit [InnerProductSpace ℂ K] in
theorem input_value (read : Orbit →ₗ[ℤ] K) (environment : Env (Value K) Var) :
    (inputTerm read).eval environment = environment Slot.measured PUnit.unit +
      read (PaidSourceMacroHistory.programme.eval (oldEnvironment environment) -
        oldEnvironment environment PaidSourceMacroHistory.Slot.orbit PUnit.unit) := by
  change environment Slot.measured PUnit.unit + (oldIncrementTerm read).eval environment = _
  rw [old_increment_value]
theorem expression_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (read : Orbit →ₗ[ℤ] K) (source : ι → K) (environment : Env (Value K) Var) :
    (expression read source).eval environment =
      (PaidSourceMacroHistory.programme.eval (oldEnvironment environment),
        FG.innovationCLM source ((inputTerm read).eval environment)) := by
  change (outputEmbed PaidSourceMacroHistory.programme).eval environment +
    measuredInjection (FG.innovationCLM source ((inputTerm read).eval environment)) = _
  rw [output_embed_eval]
  apply Prod.ext
  · exact add_zero _
  · exact zero_add _

variable (read : Orbit →ₗ[ℤ] K) (frame : Frame (K:=K))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current:=current))

omit [InnerProductSpace ℂ K] in
theorem request_row (index : Index frame) :
    source read frame (before frame supplied) index =
      ((requests frame).get index).coefficient •
        (read (((requests frame).get index).expression.eval (before frame supplied)).1 +
          (((requests frame).get index).expression.eval (before frame supplied)).2) := rfl
omit [InnerProductSpace ℂ K] in
theorem actual_request_origin (index : Index frame) :
    ∃ stock, frame.inventory=some stock ∧
      ∃ front back, stock.trace = front++((requests frame).get index).sourceEvent::back ∧
        ((requests frame).get index).position=front.length ∧
        (((requests frame).get index).expression,((requests frame).get index).coefficient) ∈
          SourceInventoryExecutionFeed.eventItems ((requests frame).get index).sourceEvent := by
  have present := List.get_mem (requests frame) index
  cases same : frame.inventory with
  | none =>
      have impossible : index.val < 0 := by simpa [requests,same] using index.isLt
      omega
  | some stock =>
      refine ⟨stock,rfl,?_⟩
      apply SourceInventoryExecutionFeed.request_origin
      have stocksame : requests frame=SourceInventoryExecutionFeed.requests stock := by
        simp only [requests,same]
      rw [← stocksame]
      exact present
theorem actual_equation :
    SourceGeneratedFiniteGram.action (FG.gram (source read frame (before frame supplied)))
      (FG.coefficients (source read frame (before frame supplied)) ((inputTerm read).eval (after frame supplied))) =
    FG.rhs (source read frame (before frame supplied)) ((inputTerm read).eval (after frame supplied)) :=
  FG.equation _ _
theorem actual_full_fibre (coefficients : SourceGeneratedFiniteGram.Coordinates (Index frame)) :
    SourceGeneratedFiniteGram.action (FG.gram (source read frame (before frame supplied))) coefficients =
      FG.rhs (source read frame (before frame supplied)) ((inputTerm read).eval (after frame supplied)) ↔
    coefficients-FG.coefficients (source read frame (before frame supplied)) ((inputTerm read).eval (after frame supplied)) ∈
      SourceGeneratedFiniteGram.Kernel (FG.gram (source read frame (before frame supplied))) :=
  FG.full_fibre _ _ coefficients

theorem scalar_value : (scalarResult read frame supplied).2.2.1 =
    (expression read (source read frame (before frame supplied))).eval (after frame supplied) :=
  O.source_value _ _ _
theorem pair_value : (pairResult read frame supplied).2.2.1 =
    (pairRaw read frame supplied).expression.eval (pairRaw read frame supplied).environment :=
  O.source_value _ _ _
theorem paid_pair_sum : (pairResult read frame supplied).2.2.1.1 +
    (pairResult read frame supplied).2.2.1.2 = (scalarResult read frame supplied).2.2.1 := by
  rw [pair_value,scalar_value]
  unfold pairRaw
  rw [eval_liftExpr]
  have updated := Expr.eval_update (expression read (source read frame (before frame supplied)))
    (before frame supplied) ((after frame supplied)-(before frame supplied))
  rw [add_sub_cancel] at updated
  exact updated.symm
theorem scalar_joint_value : (scalarResult read frame supplied).2.2.1 =
    (PaidSourceMacroHistory.programme.eval (oldEnvironment (after frame supplied)),
      FG.innovationCLM (source read frame (before frame supplied)) ((inputTerm read).eval (after frame supplied))) :=
  (scalar_value read frame supplied).trans (expression_value _ _ _)
theorem residual_orthogonal : (scalarResult read frame supplied).2.2.1.2 ∈
    (SourceGeneratedFiniteGram.Projection.sourceSpan (source read frame (before frame supplied)))ᗮ := by
  rw [scalar_joint_value]
  exact FG.innovation_orthogonal _ _
theorem paid_trace : (scalarResult read frame supplied).2.1.2.length =
    remaining (expression read (source read frame (before frame supplied))) :=
  O.source_history _ _ _
theorem paid_pair_trace : (pairResult read frame supplied).2.1.2.length =
    remaining (liftExpr (expression read (source read frame (before frame supplied)))) :=
  O.source_history _ _ _
omit [InnerProductSpace ℂ K] in
theorem after_environment : after frame supplied = frame.environment (frame.old.root.emitted current.1) := by
  rcases supplied with ⟨support,event⟩
  cases event
  exact add_sub_cancel _ _

theorem actual_pair : (S.resultFace frame (configuration read)).rootRead.2.2.1 =
    (pairResult read (A.epoch frame) (S.actualOccurrence frame)).2.2.1 := by
  have actual := O.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (configuration read)).toAuthoritativeRoot
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame (configuration read)).reader
    (S.actualOccurrence frame)
  exact actual.trans (pair_value read (A.epoch frame) (S.actualOccurrence frame)).symm
theorem born_environment {nextCurrent : (S.nextBorn frame (configuration read)).V.Current}
    (occurrence : (S.nextBorn frame (configuration read)).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt nextCurrent) :
    (S.nextBorn frame (configuration read)).environment occurrence =
      decode ((S.resultFace frame (configuration read)).rootRead.2.2.1.1+
        (S.resultFace frame (configuration read)).rootRead.2.2.1.2) := rfl
theorem born_active : (S.nextBorn frame (configuration read)).activeEnvironment =
    decode ((S.resultFace frame (configuration read)).rootRead.2.2.1.1+
      (S.resultFace frame (configuration read)).rootRead.2.2.1.2) := by
  apply SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
  intro nextCurrent occurrence
  exact born_environment read frame occurrence
theorem born_measured : (S.nextBorn frame (configuration read)).activeEnvironment Slot.measured PUnit.unit =
    (S.resultFace frame (configuration read)).rootRead.2.2.1.1.2+
      (S.resultFace frame (configuration read)).rootRead.2.2.1.2.2 := rfl
theorem born_old (sort : OldSlot) (name : OldVar sort) :
    (S.nextBorn frame (configuration read)).activeEnvironment (.old sort) name =
      PaidSourceMacroHistory.environmentAt
        ((S.resultFace frame (configuration read)).rootRead.2.2.1.1.1+
          (S.resultFace frame (configuration read)).rootRead.2.2.1.2.1) sort name := rfl

/-- This is the variable occurrence in the next joint programme, with the
newly paid residual as its actual source value. -/
theorem next_request_input : (inputTerm read).eval (S.nextBorn frame (configuration read)).activeEnvironment =
    ((S.resultFace frame (configuration read)).rootRead.2.2.1.1.2+
      (S.resultFace frame (configuration read)).rootRead.2.2.1.2.2) +
      read (PaidSourceMacroHistory.programme.eval
        (oldEnvironment (S.nextBorn frame (configuration read)).activeEnvironment) -
        oldEnvironment (S.nextBorn frame (configuration read)).activeEnvironment PaidSourceMacroHistory.Slot.orbit PUnit.unit) := by
  rw [input_value,born_measured]
theorem next_after :
    after (A.epoch (S.nextBorn frame (configuration read)))
      (S.actualOccurrence (S.nextBorn frame (configuration read))) =
    (S.nextBorn frame (configuration read)).activeEnvironment :=
  (after_environment _ _).trans
    ((born_environment read frame _).trans (born_active read frame).symm)

/-- The next wrapped receipt action registers and executes the joint body
generated from its own actual stock. Its measured argument contains the
residual written by this occurrence, not an independently evaluated term. -/
theorem next_wrapped_registered_action :
    (SourceGeneratedInquiryReceiptAction.actualMaterial (S.nextBorn frame (configuration read))
      (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).raw =
      liftExpr (expression read (source read (A.epoch (S.nextBorn frame (configuration read)))
        (before (A.epoch (S.nextBorn frame (configuration read)))
          (S.actualOccurrence (S.nextBorn frame (configuration read)))))) ∧
    (SourceGeneratedInquiryReceiptAction.actionResultAt (S.nextBorn frame (configuration read))
      (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))
      (S.actualOccurrence (S.nextBorn frame (configuration read)))).2.2.1.1 +
    (SourceGeneratedInquiryReceiptAction.actionResultAt (S.nextBorn frame (configuration read))
      (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))
      (S.actualOccurrence (S.nextBorn frame (configuration read)))).2.2.1.2 =
      (PaidSourceMacroHistory.programme.eval
        (oldEnvironment (S.nextBorn frame (configuration read)).activeEnvironment),
       FG.innovationCLM (source read (A.epoch (S.nextBorn frame (configuration read)))
         (before (A.epoch (S.nextBorn frame (configuration read)))
           (S.actualOccurrence (S.nextBorn frame (configuration read)))))
         (((S.resultFace frame (configuration read)).rootRead.2.2.1.1.2+
      (S.resultFace frame (configuration read)).rootRead.2.2.1.2.2) +
           read (PaidSourceMacroHistory.programme.eval
             (oldEnvironment (S.nextBorn frame (configuration read)).activeEnvironment) -
             oldEnvironment (S.nextBorn frame (configuration read)).activeEnvironment
               PaidSourceMacroHistory.Slot.orbit PUnit.unit))) := by
  constructor
  · rfl
  · have same :
        (SourceGeneratedInquiryReceiptAction.actionResultAt (S.nextBorn frame (configuration read))
          (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))
          (S.actualOccurrence (S.nextBorn frame (configuration read)))).2.2.1 =
        (pairResult read (A.epoch (S.nextBorn frame (configuration read)))
          (S.actualOccurrence (S.nextBorn frame (configuration read)))).2.2.1 := by
      have actual := O.source_value
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
          (S.nextBorn frame (configuration read))
          (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).toAuthoritativeRoot
        (SourceGeneratedInquiryReceiptAction.actionReader (S.nextBorn frame (configuration read))
          (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read)))
        (S.actualOccurrence (S.nextBorn frame (configuration read)))
      exact actual.trans
        (pair_value read (A.epoch (S.nextBorn frame (configuration read)))
          (S.actualOccurrence (S.nextBorn frame (configuration read)))).symm
    rw [same,paid_pair_sum,scalar_joint_value,next_after,next_request_input]

theorem born_inventory : (S.nextBorn frame (configuration read)).inventory = nextInventory read frame := rfl
theorem born_pair_inventory : (S.nextBorn frame (configuration read)).pairInventory = nextPairInventory read frame := rfl
theorem new_trace_consumed (event) (present : event ∈ (scalarWritten read frame).trace) :
    event ∈ ((S.nextBorn frame (configuration read)).inventory.getD (scalarWritten read frame)).trace := by
  rw [born_inventory]
  unfold nextInventory
  cases frame.inventory with
  | none => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
  | some prior =>
      exact (SourceHistoryCommon.parallel_right _ _ _).1 event
        ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem new_pair_consumed (event) (present : event ∈ (pairWritten read frame).trace) :
    event ∈ ((S.nextBorn frame (configuration read)).pairInventory.getD (pairWritten read frame)).trace := by
  rw [born_pair_inventory]
  unfold nextPairInventory
  cases frame.pairInventory with
  | none => exact present
  | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_inventory_consumed (prior) (same : frame.inventory=some prior)
    (event) (present : event∈prior.trace) :
    event∈((S.nextBorn frame (configuration read)).inventory.getD prior).trace := by
  rw [born_inventory]
  unfold nextInventory
  rw [same]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem old_pair_consumed (prior) (same : frame.pairInventory=some prior)
    (event) (present : event∈prior.trace) :
    event∈((S.nextBorn frame (configuration read)).pairInventory.getD prior).trace := by
  rw [born_pair_inventory]
  unfold nextPairInventory
  rw [same]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem registered_joint_expression :
    (SourceGeneratedInquiryReceiptAction.actualMaterial frame (configuration read)).raw =
      liftExpr (expression read
        (source read (A.epoch frame) (before (A.epoch frame) (S.actualOccurrence frame)))) := rfl
theorem registered_inventory_joint_expression :
    (SourceGeneratedInquiryReceiptAction.actualMaterial frame
      (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).raw =
      liftExpr (expression read
        (source read (A.epoch frame) (before (A.epoch frame) (S.actualOccurrence frame)))) := rfl
theorem inventory_calculation_reader :
    ((SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read)).datum frame).calculationReader =
      some (fun {_sourceCurrent} occurrence => reader read frame occurrence) := rfl
theorem registered_joint_input :
    (SourceGeneratedInquiryReceiptAction.registered frame (configuration read)).input.expression =
      RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
        (SourceGeneratedInquiryReceiptAction.actualMaterial frame (configuration read)) := rfl
theorem registered_joint_source : type_of%
    (SourceGeneratedInquiryReceiptAction.actual_updated_environment frame (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.actual_updated_environment frame (configuration read)

theorem wrapped_born_measured (read : Orbit →ₗ[ℤ] K) (sourceFrame : Frame (K:=K)) :
    (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).activeEnvironment Slot.measured PUnit.unit=
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.1.2+
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.2.2 := by
  simp only [SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.activeEnvironment,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environmentAt,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.environmentAt,
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,
    SourceGeneratedInquiryReceiptAction.Inventory.programme,configuration,decode,environmentFrom,Prod.snd_add]

theorem wrapped_born_environment_measured (read : Orbit →ₗ[ℤ] K) (sourceFrame : Frame (K:=K))
    {nextCurrent : (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).V.Current}
    (occurrence : (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt nextCurrent) :
    (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).environment occurrence Slot.measured PUnit.unit=
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.1.2+
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.2.2 := by
  simp only [SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn,
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,
    SourceGeneratedInquiryReceiptAction.Inventory.programme,configuration,decode,environmentFrom,Prod.snd_add]

theorem wrapped_after_measured (read : Orbit →ₗ[ℤ] K) (sourceFrame : Frame (K:=K)) :
    after (A.epoch (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))))
      (S.actualOccurrence (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read)))) Slot.measured PUnit.unit=
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.1.2+
      (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch sourceFrame) (configuration read)
        (S.actualOccurrence sourceFrame)).2.2.1.2.2 := by
  have source := after_environment (A.epoch (S.nextBorn sourceFrame
    (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))))
    (S.actualOccurrence (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))))
  have projected := congrArg (fun env : Env (Value K) Var => env Slot.measured PUnit.unit) source
  apply projected.trans
  change (S.nextBorn sourceFrame (SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read))).environment _ Slot.measured PUnit.unit = _
  exact wrapped_born_environment_measured read sourceFrame _

namespace Phase
namespace Clock
export SourceRegisteredClaimClock (sourceRemainder sourceBudget remainder_generated currentRuntime suffixHistory runtime_advance source_current source_suffix_factorizes)
end Clock

omit [InnerProductSpace ℂ K] in
def stop (frame : Frame (K:=K)) : Frame (K:=K) :=
  {frame with depth := frame.depth+Clock.sourceRemainder frame}
omit [InnerProductSpace ℂ K] in
theorem stop_zero (frame : Frame (K:=K)) : remaining (stop frame).event.state.1=0 := by
  change Clock.sourceRemainder (stop frame)=0
  rw [Clock.remainder_generated]
  change Clock.sourceBudget frame-(frame.depth+Clock.sourceRemainder frame+1)=0
  have original := Clock.remainder_generated frame
  omega
omit [InnerProductSpace ℂ K] in
def settlement (frame : Frame (K:=K)) :=
  RootGeneratedDebtActivationJointSource.localSettlement (stop frame).event (stop_zero frame)
omit [InnerProductSpace ℂ K] in
theorem stop_action (frame : Frame (K:=K)) : (stop frame).action=.inl (settlement frame) := by
  cases actual : (stop frame).action with
  | inl chosen =>
      have unique : chosen=settlement frame := by
        rcases chosen with ⟨first,⟨firstEq⟩⟩
        rcases settlement frame with ⟨second,⟨secondEq⟩⟩
        have same : first=second := Expr.const.inj (firstEq.symm.trans secondEq)
        cases same
        rfl
      exact congrArg Sum.inl unique
  | inr paid =>
      have strict := (RootGeneratedDebtActivationJointSource.law (stop frame).registered).step_budget_lt paid.2
      change remaining paid.1.1 < remaining (stop frame).event.state.1 at strict
      rw [stop_zero] at strict
      omega
omit [InnerProductSpace ℂ K] in
theorem stop_fields (frame : Frame (K:=K)) :
    (stop frame).registered=frame.registered ∧
      (∀ {phaseCurrent : frame.V.Current} (occurrence : frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt phaseCurrent),
        (stop frame).environment occurrence=frame.environment occurrence) ∧
      (stop frame).inventory=frame.inventory ∧ (stop frame).pairInventory=frame.pairInventory := ⟨rfl,(by intros; rfl),rfl,rfl⟩
omit [InnerProductSpace ℂ K] in
theorem suffix_target (frame : Frame (K:=K)) :
    (Clock.suffixHistory frame).target=Clock.currentRuntime (stop frame) := by
  change (Clock.currentRuntime frame).advance (Clock.sourceRemainder frame)=_
  rw [Clock.currentRuntime,Clock.runtime_advance]
  change SourceRegisteredClaimClock.C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
    (frame.depth+1+Clock.sourceRemainder frame)=
    SourceRegisteredClaimClock.C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
    (frame.depth+Clock.sourceRemainder frame+1)
  congr 1; omega
omit [InnerProductSpace ℂ K] in
theorem suffix_current (frame : Frame (K:=K)) :
    (stop frame).currentState.visit.current=
      RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
        frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (Clock.suffixHistory frame).target := by
  rw [suffix_target]
  change (RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit frame.old frame.registered frame.packetAt
    ((stop frame).depth+1)).current=
    RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
      (SourceRegisteredClaimClock.C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt ((stop frame).depth+1))
  rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent,
    SourceRegisteredClaimClock.C.runtime_depth]
  exact Clock.source_current frame _

variable (read : Orbit →ₗ[ℤ] K) (frame : Frame (K:=K))
abbrev wrapped := SourceGeneratedInquiryReceiptAction.Inventory.programme (configuration read)
def paidPair : PairValue (Value K) Slot.joint :=
  (SourceGeneratedInquiryReceiptAction.Inventory.lowResult (A.epoch (stop frame)) (configuration read)
    (S.actualOccurrence (stop frame))).2.2.1
def paidResidual : K := (paidPair read frame).1.2+(paidPair read frame).2.2
theorem next_is_birth : S.next (stop frame) (wrapped read)=S.nextBorn (stop frame) (wrapped read) := by
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  rw [stop_action]
theorem next_measured :
    (S.nextBorn (stop frame) (wrapped read)).activeEnvironment Slot.measured PUnit.unit=paidResidual read frame := by
  simpa only [wrapped,paidResidual,paidPair] using wrapped_born_measured read (stop frame)
theorem next_source_after_measured :
    after (A.epoch (S.nextBorn (stop frame) (wrapped read)))
      (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit=
    paidResidual read frame := by
  simpa only [wrapped,paidResidual,paidPair] using wrapped_after_measured read (stop frame)
theorem registered_environment :
    (SourceGeneratedInquiryReceiptAction.registered (stop frame) (wrapped read)).input.environment=
      (reader read (A.epoch (S.nextBorn (stop frame) (wrapped read)))
        (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read)))).environment := by
  apply (SourceGeneratedInquiryReceiptAction.actual_updated_environment (stop frame) (wrapped read)).trans
  unfold SourceGeneratedInquiryReceiptAction.afterEnvironment
  rw [next_is_birth]
  rfl
theorem registered_measured :
    ((SourceGeneratedInquiryReceiptAction.registered (stop frame) (wrapped read)).input.environment Slot.measured PUnit.unit).1+
      ((SourceGeneratedInquiryReceiptAction.registered (stop frame) (wrapped read)).input.environment Slot.measured PUnit.unit).2=
    paidResidual read frame := by
  rw [registered_environment]
  change
    before (A.epoch (S.nextBorn (stop frame) (wrapped read)))
      (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit +
    (after (A.epoch (S.nextBorn (stop frame) (wrapped read)))
      (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit -
     before (A.epoch (S.nextBorn (stop frame) (wrapped read)))
      (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit) = _
  have balanced :
      before (A.epoch (S.nextBorn (stop frame) (wrapped read)))
        (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit +
      (after (A.epoch (S.nextBorn (stop frame) (wrapped read)))
        (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit -
       before (A.epoch (S.nextBorn (stop frame) (wrapped read)))
        (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit) =
      after (A.epoch (S.nextBorn (stop frame) (wrapped read)))
        (S.actualOccurrence (S.nextBorn (stop frame) (wrapped read))) Slot.measured PUnit.unit := by abel
  exact balanced.trans (next_source_after_measured read frame)
abbrev actualBorn := SourceGeneratedInquiryReceiptAction.Inventory.Born.bornFrame (stop frame) (configuration read)
theorem born_raw_measured :
    ((actualBorn read frame).rawRead.environment Slot.measured PUnit.unit).1+
      ((actualBorn read frame).rawRead.environment Slot.measured PUnit.unit).2=paidResidual read frame :=
  registered_measured read frame
omit [InnerProductSpace ℂ K] in
theorem source_suffix : type_of% (Clock.source_suffix_factorizes frame) := Clock.source_suffix_factorizes frame
abbrev canonical := SourceGeneratedInquiryReceiptAction.Inventory.Born.generated (stop frame) (configuration read)
theorem canonical_next : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next
    (stop frame) (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next (stop frame) (configuration read)
theorem canonical_whole : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first
    (stop frame) (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first (stop frame) (configuration read)

/-- The paid suffix determines the exact source occurrence used by the real
registration and by the independent Born consumer. -/
def generated :=
  (Clock.suffixHistory frame, (⟨suffix_target frame⟩ : PLift ((Clock.suffixHistory frame).target=Clock.currentRuntime (stop frame))),
    (⟨suffix_current frame⟩ : PLift ((stop frame).currentState.visit.current=
      RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
        frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (Clock.suffixHistory frame).target)),
    stop frame,settlement frame,
    (⟨source_suffix frame⟩ : PLift (_)),
    (⟨next_is_birth read frame⟩ : PLift (_)),
    (⟨registered_measured read frame⟩ : PLift (_)),
    (⟨born_raw_measured read frame⟩ : PLift (_)),canonical read frame)
end Phase

/-- The existing independent receipt consumer takes this joint registered
programme, including its new paid inventory, through whole and next. -/
abbrev actual_joint_innovation_next := Phase.generated read frame
theorem actual_whole : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first frame (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.whole_first frame (configuration read)
theorem actual_next : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next frame (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.literal_next frame (configuration read)
theorem no_refill : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.no_refill frame (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.no_refill frame (configuration read)
theorem noetherian : type_of% (SourceGeneratedInquiryReceiptAction.Inventory.Born.noetherian frame (configuration read)) :=
  SourceGeneratedInquiryReceiptAction.Inventory.Born.noetherian frame (configuration read)

namespace Actual
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
variable (word : PaidSourceMacroHistory.Word.{u}) (stage cut offset : Nat)

abbrev actual_joint_innovation_next := JointMeasured.actual_joint_innovation_next
  (actualRead root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut)
  (frameAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut offset)
theorem actual_next_request_input : type_of% (Phase.born_raw_measured
    (actualRead root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut)
    (frameAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut offset)) :=
  Phase.born_raw_measured _ _
theorem actual_registered_joint : type_of% (registered_inventory_joint_expression
    (actualRead root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut)
    (Phase.stop (frameAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut offset))) :=
  registered_inventory_joint_expression _ _
theorem actual_old_occurrence : (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut).toAuthoritativeRoot.toLedgerRoot =
    (oldSourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage).toAuthoritativeRoot.toLedgerRoot := rfl
theorem initial_old_next :
    (paidAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut
      (oldOccurrence root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage)).2.2.1.1 =
      PaidSourceMacroHistory.programme.eval
        (oldFrame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage).activeEnvironment := by
  have actual := O.source_value
    (oldSourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage).toAuthoritativeRoot
    (rawAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut)
    (oldOccurrence root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage)
  exact (congrArg Prod.fst actual).trans (congrArg Prod.fst (seed_expression_value _ _))
end Actual
end PaidSourceContentEnvironment.JointMeasured
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
