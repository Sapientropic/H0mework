import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Linear.Receiver.Source
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace FullSourceReceiverLinearAction
-- The successor environment is read from its own occurrence; the complete effect is retained in write-back.
section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace SR
export RootGeneratedDebtActivationJointSource.Successor.Restructuring (projectionLaw projection_original)
end SR
namespace R
export SourceGeneratedInquiryReceiptAction (actionResultAt)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualOccurrence)
end S
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)
variable {current : C.Current (Next.receiver frame cfg).registered}
variable (supplied : I.Occurrence (Next.receiver frame cfg) (current := current))

def currentNativeResult := (receiverCommonAt frame cfg supplied).2.2
def currentCompleteMaterial := (receiverCommonAt frame cfg supplied).1

theorem receiver_projection_original : type_of% (SR.projection_original
 (Next.receiver frame cfg).old.root.toAuthoritativeRoot
 (Next.receiver frame cfg).registered (Next.receiver frame cfg).packetAt supplied
 ((Q.commonInstalled frame cfg).embed PUnit.unit)) :=
 SR.projection_original (Next.receiver frame cfg).old.root.toAuthoritativeRoot
 (Next.receiver frame cfg).registered (Next.receiver frame cfg).packetAt supplied
 ((Q.commonInstalled frame cfg).embed PUnit.unit)

theorem receiver_epoch_at_depth (depth : Nat) :
 A.epoch ({Next.receiver frame cfg with depth := depth}) = A.epoch (Next.receiver frame cfg) := rfl

theorem reader_at_depth (depth : Nat) :
 R.actionReader ({Next.receiver frame cfg with depth := depth}) (programme frame cfg action) supplied =
 currentLinearRaw frame cfg action supplied := by
 change R.actionReader (A.epoch ({Next.receiver frame cfg with depth := depth})) (lowProgramme frame cfg action) supplied = _
 have datum : (lowProgramme frame cfg action).datum
   (A.epoch (A.epoch ({Next.receiver frame cfg with depth := depth}))) = receiverDatum frame cfg action := by
  change (lowProgramme frame cfg action).datum (A.epoch (A.epoch (Next.receiver frame cfg))) = _
  exact datum_actual_epoch frame cfg action
 unfold R.actionReader SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
 rw [datum]
 rfl

private theorem full_raw_zero_effect (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue Value) (Var := cfg.LowVar) (sort := s)) :
 raw.expression.effect raw.environment 0 = 0 := by
 have generated := Expr.eval_update raw.expression raw.environment 0
 rw [add_zero] at generated
 exact add_left_cancel (generated.symm.trans (add_zero _).symm)

theorem current_linear_value :
 (currentLinearRaw frame cfg action supplied).expression.eval (currentLinearRaw frame cfg action supplied).environment =
 action ((currentFullRaw frame cfg supplied).expression.eval (currentFullRaw frame cfg supplied).environment, 0) := by
 change action ((liftExpr (currentFullRaw frame cfg supplied).expression).eval
  (pairEnvironment (currentFullRaw frame cfg supplied).environment 0)) = _
 exact congrArg action ((eval_liftExpr _ _ _).trans
  (congrArg (fun effect => ((currentFullRaw frame cfg supplied).expression.eval
   (currentFullRaw frame cfg supplied).environment, effect))
   (full_raw_zero_effect cfg (currentFullRaw frame cfg supplied))))

theorem current_linear_budget :
 remaining (currentLinearRaw frame cfg action supplied).expression =
 remaining (liftExpr (currentFullRaw frame cfg supplied).expression) + 1 := rfl

theorem actual_linear_value :
 (R.actionResultAt (Next.receiver frame cfg) (programme frame cfg action) supplied).2.2.1 =
 action ((currentFullRaw frame cfg supplied).expression.eval (currentFullRaw frame cfg supplied).environment, 0) := by
 have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (S.baseRoot (Next.receiver frame cfg) (programme frame cfg action)).toAuthoritativeRoot
  (R.actionReader (Next.receiver frame cfg) (programme frame cfg action)) supplied
 exact generated.trans ((congrArg
  (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue (PairValue Value)) (Var := cfg.LowVar) (sort := s) =>
   raw.expression.eval raw.environment) (reader_actual_source frame cfg action supplied)).trans
   (current_linear_value frame cfg action supplied))

end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
 (generatedAction target_root target_next compiles successor_valid)
end Intake
namespace Next
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next (fullRaw)
end Next
namespace R
export SourceGeneratedInquiryReceiptAction (sourceEvent)
end R
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)

def admitted := Intake.generatedAction frame (Q.programme cfg) (programme frame cfg action)

theorem actual_full_raw : currentFullRaw frame cfg (S.actualOccurrence (Next.receiver frame cfg)) =
 Next.fullRaw frame cfg := rfl

theorem actual_receiver_value :
 (R.actionResultAt (Next.receiver frame cfg) (programme frame cfg action)
  (S.actualOccurrence (Next.receiver frame cfg))).2.2.1 =
 action ((Next.fullRaw frame cfg).expression.eval (Next.fullRaw frame cfg).environment, 0) := by
 have generated := actual_linear_value frame cfg action (S.actualOccurrence (Next.receiver frame cfg))
 rw [actual_full_raw] at generated
 exact generated

theorem actual_emitter_root : type_of% (Intake.target_root frame (Q.programme cfg) (programme frame cfg action)
 (R.sourceEvent frame (Q.programme cfg))) :=
 Intake.target_root frame (Q.programme cfg) (programme frame cfg action) (R.sourceEvent frame (Q.programme cfg))

theorem actual_emitter_current : type_of% (Intake.target_next frame (Q.programme cfg) (programme frame cfg action)
 (R.sourceEvent frame (Q.programme cfg))) :=
 Intake.target_next frame (Q.programme cfg) (programme frame cfg action) (R.sourceEvent frame (Q.programme cfg))

theorem actual_emitter_compiles : type_of% (Intake.compiles frame (Q.programme cfg) (programme frame cfg action)) :=
 Intake.compiles frame (Q.programme cfg) (programme frame cfg action)

theorem actual_emitter_next : type_of% (Intake.successor_valid frame (Q.programme cfg) (programme frame cfg action)) :=
 Intake.successor_valid frame (Q.programme cfg) (programme frame cfg action)

theorem actual_emitter_whole : type_of% (admitted frame cfg action).target.firstDestination_heq :=
 (admitted frame cfg action).target.firstDestination_heq

end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end S
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)

abbrev selected := Complete.atReceipt (programme frame cfg action) (Next.receiver frame cfg) 0

theorem selected_epoch : A.epoch (selected frame cfg action) = A.epoch (Next.receiver frame cfg) := by
 apply Prefix.receipt_read (programme frame cfg action) (Next.receiver frame cfg)
  (fun stage => A.epoch (S.frames (Next.receiver frame cfg) (programme frame cfg action) stage)) _ 0
 intro stage paid actual
 have next : S.frames (Next.receiver frame cfg) (programme frame cfg action) (stage+1) =
  (S.frames (Next.receiver frame cfg) (programme frame cfg action) stage).mathNext := by
  change S.next _ _ = _
  unfold S.next
  rw [actual]
 exact (congrArg A.epoch next).trans (by rfl)

private theorem datum_heq
 {first second : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PairValue Value) (Var := cfg.LowVar) (sort := s)}
 (same : first = second) :
 HEq ((lowProgramme frame cfg action).datum first) ((lowProgramme frame cfg action).datum second) := by
 cases same
 rfl

theorem selected_datum : HEq
 ((lowProgramme frame cfg action).datum (A.epoch (selected frame cfg action)))
 (receiverDatum frame cfg action) :=
 (datum_heq frame cfg action (selected_epoch frame cfg action)).trans
 (heq_of_eq (by change (lowProgramme frame cfg action).datum (A.epoch (A.epoch (Next.receiver frame cfg))) = _
                exact datum_actual_epoch frame cfg action))

end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)

theorem actual_updated_value :
 (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw.eval
  (N.input (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action))).environment =
 (R.actionResultAt (Next.receiver frame cfg) (programme frame cfg action)
  (S.actualOccurrence (Next.receiver frame cfg))).2.2.1 +
 (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw.effect
  (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).environment
  (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).increment := by
 have initial := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (S.baseRoot (Next.receiver frame cfg) (programme frame cfg action)).toAuthoritativeRoot
  (R.actionReader (Next.receiver frame cfg) (programme frame cfg action))
  (S.actualOccurrence (Next.receiver frame cfg))
 exact (Expr.eval_update
  (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw
  (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).environment
  (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).increment).trans
  (congrArg (fun value => value +
   (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw.effect
    (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).environment
    (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).increment) initial.symm)

end

end FullSourceReceiverLinearAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
