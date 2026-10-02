import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Inquiry

/-! The activated mother source reads the already paid full calculation.
Its strict debit is derived from the same selected stage and destination;
settled stages preserve their whole transport and canonical next. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence actualVisit resultFace)
end S
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (destination_math)
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))

abbrev occurrence := S.actualOccurrence frame
abbrev receipts := (face frame).rootRead.2
abbrev stageState (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  state (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame) count.1
abbrev stageRoot := calculationRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame)

def mathEntryAt (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  O.mathEntry (originRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
    (S.actualVisit frame).current
    (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame))
    (stageState frame count)

def destination (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  ((receipts frame).whole count).destination (mathEntryAt frame count)

def stepOutcome (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  (receipts frame).action count

theorem destination_generated (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    (destination frame count).1 =
      O.mathEntry (originRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
        (S.actualVisit frame).current
        (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame))
        (O.nextState (originRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
          (S.actualVisit frame).current
          (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame))
          (stageState frame count)) :=
  O.destination_math _ _ _ _

theorem no_refill (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    (destination frame count).1.progressBudget ≤ (mathEntryAt frame count).progressBudget :=
  (destination frame count).2.progressBudget_not_refilled

def payment (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  generatePayment (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame) count

theorem material_stage_read (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq ((receipts frame).material count).1.1
      (stage (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame) count).activated.generated.wholeLedgerWriteBack :=
  material_stage (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame) count

theorem stage_clock (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    ((O.Calculation.seed (originRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
      (S.actualVisit frame).current
      (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame))).advance count.1).state.down = count.1 :=
  stage_depth (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame) count

abbrev actualResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (S.baseRoot frame chargedProgramme).toAuthoritativeRoot ((S.datum frame chargedProgramme).reader) (occurrence frame)

theorem result_state_receipt : HEq (actualResult frame).2.1
    (state frame (occurrence frame) (remaining (receipts frame).raw.expression + 1)) := by
  change HEq (chargedState frame (remaining (receipts frame).raw.expression + 1)) _
  exact heq_of_eq (charged_state frame _)

theorem actual_result : (S.resultFace frame chargedProgramme).rootRead = actualResult frame := rfl

theorem charged_write_receipt (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (O.whole (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) (chargedState frame count.1))
      ((receipts frame).whole count) := charged_whole frame count.1

def chargedCertificate (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.tickCertificate
    (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current (commonReader frame)
    (O.Completion.runtime (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) count.1)

def chargedStage (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  SourceGeneratedRuntimeMaterialStageAt.generate
    (O.Completion.runtime (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) count.1)

theorem charged_stage_factorizes (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    type_of% ((chargedStage frame count).factorizes) := (chargedStage frame count).factorizes

def chargedMaterial (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
    (O.authoritativeRoot (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame))
    ((O.authoritativeRoot (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame)).emitted (chargedState frame count.1))

theorem charged_material_stage (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (chargedMaterial frame count).1.1 (chargedStage frame count).wholeLedgerWriteBack := HEq.rfl

theorem charged_history_stage (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (chargedStage frame count)
      ((O.Calculation.frontier (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
        (S.actualVisit frame).current (commonReader frame)).history.stageAt count) := HEq.rfl

theorem charged_stage_clock (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    (O.Completion.runtime (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
      (S.actualVisit frame).current (commonReader frame) count.1).state.down = count.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime_depth
    (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current (commonReader frame) count.1

theorem old_observation : (S.root frame chargedProgramme).source.base.observationAt (occurrence frame) =
    (S.base frame).root.source.base.observationAt (occurrence frame) := rfl

theorem original_inventory : (face frame).rootRead.1.original =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      frame.currentState.root.toAuthoritativeRoot (occurrence frame) := rfl

def settled : SourceOperationExecutionDebt.Settlement (actualResult frame).2.1 :=
  ⟨(actualResult frame).2.2.1,
    ⟨RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression
      (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current
      (commonReader frame)⟩⟩

theorem settled_value : (settled frame).1 = (receipts frame).raw.expression.eval (receipts frame).raw.environment :=
  SourceOperationExecutionDebt.completed_value (actualResult frame).2.1 (settled frame)

theorem settled_action : ∃ localSettlement,
    O.action (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current
      (commonReader frame) (actualResult frame).2.1 = .inl localSettlement := by
  cases actual : O.action (S.baseRoot frame chargedProgramme).toAuthoritativeRoot (S.actualVisit frame).current
      (commonReader frame) (actualResult frame).2.1 with
  | inl localSettlement => exact ⟨localSettlement, rfl⟩
  | inr paid =>
      have zero := (O.law (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
        (S.actualVisit frame).current (commonReader frame)).settlement_budget_zero (settled frame)
      have strict := (O.law (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
        (S.actualVisit frame).current (commonReader frame)).step_budget_lt paid.2
      rw [zero] at strict
      exact False.elim (Nat.not_lt_zero _ strict)

def lastSettlement : SourceOperationExecutionDebt.Settlement
    (stageState frame ⟨remaining (receipts frame).raw.expression, Nat.lt_succ_self _⟩) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Completion.localSettlement _ _ _ _
    (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completed_budget
      (originRoot (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
      (S.actualVisit frame).current
      (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (occurrence frame)))

variable (initial : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem actual_query (count : Nat) : HEq ((runtime initial).stateAt count).activation.query
    (S.query (frames initial count) chargedProgramme) := S.actual_query initial chargedProgramme count

theorem actual_answer (count : Nat) : HEq ((runtime initial).tickAt count).answer
    ((S.state (frames initial count) chargedProgramme).compileInquiry
      (S.query (frames initial count) chargedProgramme)).answerReadout := S.actual_answer initial chargedProgramme count

theorem actual_next (count : Nat) : ((runtime initial).tickAt count).next.node =
    .active (S.presentation (frames initial (count + 1)) chargedProgramme) := S.actual_next initial chargedProgramme count

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
