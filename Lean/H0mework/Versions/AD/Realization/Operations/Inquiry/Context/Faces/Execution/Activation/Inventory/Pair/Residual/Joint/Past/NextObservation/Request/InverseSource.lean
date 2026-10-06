import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.OccurrenceConsumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
def nextEnvironment :=
  let cursor := (Action.sourceCursor frame occurrence).next.next
  pairEnvironment cursor.next.raw.environment (cursor.next.next.raw.environment-cursor.next.raw.environment)
def trace : Trace (nextEnvironment frame occurrence) (occurrenceRaw seed frame occurrence).expression
    (.const ((occurrenceRaw seed frame occurrence).expression.eval (nextEnvironment frame occurrence))) :=
  execution (nextEnvironment frame occurrence) (occurrenceRaw seed frame occurrence).expression
abbrev exposure := SourceOperationPaidRelations.exposure (trace seed frame occurrence)
def written := SourceHistoryCommon.seed (occurrenceWritten seed frame occurrence) (exposure seed frame occurrence)
variable (configuration : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort))
variable (inherited : (Shared.datum frame configuration).nextEnvironmentRead = none)

include inherited in
theorem next_environment_actual : nextEnvironment (epoch frame) (Shared.actualOccurrence frame) =
    (occurrenceRaw seed (epoch (Shared.next frame configuration))
      (Shared.actualOccurrence (Shared.next frame configuration))).environment := by
  have cursor : Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame) =
    Context.Native.Orbit.Installation.ofFrame frame := rfl
  change pairEnvironment (Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.next.raw.environment
    ((Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.next.next.raw.environment -
      (Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.next.raw.environment) = _
  have shifted := congrArg (fun c => pairEnvironment c.next.next.raw.environment
    (c.next.next.next.raw.environment-c.next.next.raw.environment))
    (Renewal.cursor_shared_next frame configuration inherited)
  apply (congrArg (fun c => pairEnvironment c.next.next.next.raw.environment
    (c.next.next.next.next.raw.environment-c.next.next.next.raw.environment)) cursor).trans
  apply shifted.trans
  have nextCursor : Action.sourceCursor (epoch (Shared.next frame configuration))
      (Shared.actualOccurrence (Shared.next frame configuration)) =
    Context.Native.Orbit.Installation.ofFrame (Shared.next frame configuration) := rfl
  exact (congrArg (fun c => pairEnvironment c.next.next.raw.environment
    (c.next.next.next.raw.environment-c.next.next.raw.environment)) nextCursor).symm

theorem complete_trace (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (exposure seed frame occurrence).trace) :
    event ∈ (written seed frame occurrence).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present

def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=sourceCurrent)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
  ⟨nextEnvironment frame supplied,(occurrenceRaw seed frame supplied).expression⟩
def result {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
    (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (reader seed frame) supplied

def paidWritten {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
  SourceHistoryCommon.seed (occurrenceWritten seed frame supplied)
    (SourceOperationPaidRelations.exposure (result seed frame supplied).2.1.2)

include inherited in
theorem next_raw_actual : reader seed (epoch frame) (Shared.actualOccurrence frame) =
    ⟨(occurrenceRaw seed (epoch (Shared.next frame configuration))
      (Shared.actualOccurrence (Shared.next frame configuration))).environment,
      (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression⟩ := by
  exact congrArg (fun environment => (⟨environment,
    (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression⟩ :
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw
        (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort)))
    (next_environment_actual seed frame configuration inherited)
theorem generated_value : (result seed frame occurrence).2.2.1 =
    (occurrenceRaw seed frame occurrence).expression.eval (nextEnvironment frame occurrence) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem generated_cost : (result seed frame occurrence).2.1.2.length =
    remaining (occurrenceRaw seed frame occurrence).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem every_paid_relation (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (SourceOperationPaidRelations.exposure (result seed frame occurrence).2.1.2).trace) :
    event ∈ (paidWritten seed frame occurrence).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem generated_boundary : SourceOperationScalarPresentation.relationMap (R:=ℤ) (nextEnvironment frame occurrence)
    (result seed frame occurrence).2.1.2.relationWords =
      Finsupp.single (occurrenceRaw seed frame occurrence).expression 1 -
        Finsupp.single (result seed frame occurrence).2.1.1 1 :=
  (result seed frame occurrence).2.1.2.relation_boundary

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
