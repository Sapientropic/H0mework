import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Occurrence
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J

theorem physical_epoch (sourceFrame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) :
    Action.updatedPairEnvironment (epoch sourceFrame) (Shared.actualOccurrence sourceFrame) =
      Action.updatedPairEnvironment sourceFrame (Shared.actualOccurrence sourceFrame) := by
  unfold Action.updatedPairEnvironment Action.sourceNextEnvironment InventoryProgramme.physical Context.Installation.materialAt
  dsimp only [epoch]
  rcases Shared.actualOccurrence sourceFrame with ⟨support,event⟩
  cases event
  unfold Context.Installation.nextRawAt Context.Installation.rawAt Context.Installation.residualAt
  cases RootGeneratedDebtActivationJointSource.mathAction (Shared.actualVisit sourceFrame).current.2 <;> rfl

include seed in
theorem cursor_pair (sourceFrame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort)) :
    pairEnvironment (Context.Native.Orbit.Installation.ofFrame sourceFrame).next.raw.environment
      ((Context.Native.Orbit.Installation.ofFrame sourceFrame).next.next.raw.environment -
        (Context.Native.Orbit.Installation.ofFrame sourceFrame).next.raw.environment) =
      Action.updatedPairEnvironment (epoch sourceFrame) (Shared.actualOccurrence sourceFrame) := by
  have first := Renewal.first_environment_actual seed sourceFrame
  have next := Renewal.cursor_shared_next sourceFrame (programme seed) rfl
  have firstRaw : (Context.Native.Orbit.Installation.ofFrame sourceFrame).next.raw.environment =
      Action.sourceNextEnvironment sourceFrame (Shared.actualOccurrence sourceFrame) :=
    (congrArg (fun cursor => cursor.raw.environment) next).trans first.symm
  have cursor : Action.sourceCursor sourceFrame (Shared.actualOccurrence sourceFrame) =
      Context.Native.Orbit.Installation.ofFrame sourceFrame := rfl
  change _ = Action.updatedPairEnvironment (epoch sourceFrame) (Shared.actualOccurrence sourceFrame)
  exact ((congrArg₂ pairEnvironment firstRaw (congrArg₂ (· - ·) rfl firstRaw)).trans
    (congrArg (fun c => pairEnvironment (Action.sourceNextEnvironment sourceFrame (Shared.actualOccurrence sourceFrame))
      (c.next.next.raw.environment - Action.sourceNextEnvironment sourceFrame (Shared.actualOccurrence sourceFrame))) cursor.symm)).trans
    (physical_epoch sourceFrame).symm

theorem occurrence_next_environment :
    (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).environment =
      (after seed frame).environment := by
  change pairEnvironment (Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.raw.environment
    ((Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.next.raw.environment -
      (Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame)).next.next.raw.environment) = _
  have cursor : Action.sourceCursor (epoch frame) (Shared.actualOccurrence frame) =
      Context.Native.Orbit.Installation.ofFrame frame := rfl
  rw [cursor]
  have move := Renewal.cursor_shared_next frame (continuedConfiguration seed) rfl
  have shifted := congrArg (fun c => pairEnvironment c.next.raw.environment
    (c.next.next.raw.environment-c.next.raw.environment)) move
  have identified :
      pairEnvironment (Context.Native.Orbit.Installation.ofFrame (actualNext seed frame)).next.raw.environment
        ((Context.Native.Orbit.Installation.ofFrame (actualNext seed frame)).next.next.raw.environment -
          (Context.Native.Orbit.Installation.ofFrame (actualNext seed frame)).next.raw.environment) =
      (after seed frame).environment := by
    apply (cursor_pair seed (actualNext seed frame)).trans
    exact (Residual.raw_environment seed (epoch (actualNext seed frame))
      (Shared.actualOccurrence (actualNext seed frame))).symm
  exact shifted.trans identified

theorem occurrence_expression :
    (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression =
      (registered seed frame).input.expression := by
  change Expr.add (Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame)).expression
    (Expr.linear (-AddMonoidHom.id _)
      (Joint.queryResult seed (epoch frame) (Shared.actualOccurrence frame)).2.1.1) = _
  have same := RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_state
    (Shared.baseRoot frame (continuedConfiguration seed)).toAuthoritativeRoot (origin frame)
    (Mother.baseState (epoch frame)).root.toAuthoritativeRoot (origin frame)
    (Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame))
    (remaining (Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame)).expression)
  have targets : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.targetState
      (Shared.baseRoot frame (continuedConfiguration seed)).toAuthoritativeRoot (origin frame)
        (fun _ => Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame)) =
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.targetState
      (Mother.baseState (epoch frame)).root.toAuthoritativeRoot (origin frame)
        (fun _ => Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame)) :=
    (RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_state _ _ _).trans
      (same.trans (RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_state _ _ _).symm)
  exact congrArg (fun state => Expr.add
    (Joint.queryReader seed (epoch frame) (Shared.actualOccurrence frame)).expression
    (Expr.linear (-AddMonoidHom.id _) state.1)) targets.symm

theorem occurrence_value :
    (occurrenceExecuted seed (epoch frame) (Shared.actualOccurrence frame)).2.2.1 =
      (completed seed frame).1 := by
  have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Mother.baseState (epoch frame)).root.toAuthoritativeRoot
    (occurrenceRaw seed (epoch frame)) (Shared.actualOccurrence frame)
  have matching : (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression.eval
      (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).environment =
      (registered seed frame).input.expression.eval (registered seed frame).input.environment := by
    rw [occurrence_expression,occurrence_next_environment,actual_next_environment]
  exact generated.trans (matching.trans
    (T.C.completed_value (calculationRoot seed frame) (registered seed frame) (packets seed frame)).symm)
theorem occurrence_fee : (occurrenceExecuted seed (epoch frame) (Shared.actualOccurrence frame)).2.1.2.length =
    remaining (registered seed frame).input.expression := by
  have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (Mother.baseState (epoch frame)).root.toAuthoritativeRoot
    (occurrenceRaw seed (epoch frame)) (Shared.actualOccurrence frame)
  exact generated.trans (congrArg remaining (occurrence_expression seed frame))

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
