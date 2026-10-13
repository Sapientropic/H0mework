import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Inventory
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeRuntimeFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace L
export OriginalKFullSourceRAction.L (Value groups)
end L
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace AS
export OriginalKFullSourceRAction.AS (AdmissionPacket)
end AS
namespace SF
export OriginalKFiniteWard.SF (Factory)
end SF
namespace N
export ActualCofinalSourceAction (nativePacket receiver_input receiver_ast selected receipt nativeValue)
end N
namespace RS
export RootGeneratedDebtActivationJointSource.Successor.Restructuring (runtimeCurrent facade rawFace rawInstallation rawLaw)
end RS
namespace Calc
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation (frontier realization seed sourceRead source_payload)
end Calc
local instance nativeGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target

private def receiverFrame
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :=
 (N.nativePacket producer packet).2.1.1

private def nativeFrontier
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :=
 let frame := receiverFrame producer packet
 Calc.frontier frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt

private theorem nativeRealization
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 SourceNativeRuntimeCalculationRealizationAt (nativeFrontier producer packet) :=
 let frame := receiverFrame producer packet
 Calc.realization frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt

private theorem native_registered_input
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (N.receiver_input producer packet) := N.receiver_input producer packet

private theorem native_stage
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
 (index : Fin ((nativeFrontier producer packet).stageCount+1)) : type_of%
 ((nativeRealization producer packet).operationAt index) :=
 (nativeRealization producer packet).operationAt index

private theorem generic_next_paid
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (paid : DebtActivationWorld.GeneratedStepAt
   (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
   frame.event.state) (actual : frame.action = .inr paid) :
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg = frame.mathNext := by
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 rw [actual]

private theorem generic_paid_prefix_frames
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (offset : Nat)
 (within : offset ≤ (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1) :
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg (0+offset) =
 { frame with depth := frame.depth + offset } := by
 induction offset with
 | zero => simp only [Nat.add_zero]; rfl
 | succ offset previous =>
   have prior := previous (Nat.le_trans (Nat.le_succ offset) within)
   let paid := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_paid_prefix
     cfg frame 0 ⟨offset,Nat.lt_of_lt_of_le (Nat.lt_succ_self offset) within⟩
   have next := generic_next_paid
     (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg (0+offset)) cfg paid.1 paid.2.down
   have shifted := congrArg (fun candidate : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
     (Value:=Value) (Var:=Var) (sort:=()) => candidate.mathNext) prior
   exact next.trans (shifted.trans (by rfl))

private theorem generic_stopping_raw_source
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg
   (0+(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1)).rawRead =
 frame.rawRead := by
 rw [generic_paid_prefix_frames _ _ _ (Nat.le_refl _)]
 rfl

private theorem stopping_raw_source
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 (N.selected producer packet).rawRead = (receiverFrame producer packet).rawRead :=
 generic_stopping_raw_source (receiverFrame producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)

private theorem generic_paid_runtime_current
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (offset : Nat)
 (within : offset ≤ (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1) :
 HEq (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg (0+offset)).currentState.visit.current
 (RS.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
     frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+offset+1))) := by
 rw [generic_paid_prefix_frames frame cfg offset within]
 unfold RS.runtimeCurrent
 rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime_depth]
 exact heq_of_eq (SourceRegisteredClaimClock.source_current {frame with depth:=frame.depth+offset} _)

private theorem stopping_full_runtime_current
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (generic_paid_runtime_current (receiverFrame producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (N.receipt producer packet).1 (Nat.le_refl _)) :=
 generic_paid_runtime_current _ _ _ (Nat.le_refl _)

private theorem generic_full_visits
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=())) (count : Nat) :
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit frame.old frame.registered frame.packetAt count =
 RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
   frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count := by
 induction count with
 | zero => rfl
 | succ count prior => exact congrArg (fun visit => visit.next (by rfl)) prior

private theorem generic_paid_runtime_visit
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (offset : Nat)
 (within : offset ≤ (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1) :
 HEq (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg (0+offset)).currentState.visit
 (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
   frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+offset+1)).current.visit := by
 rw [generic_paid_prefix_frames frame cfg offset within]
 change HEq (SourceNativeTemporalVisitAt.finite
   (RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit frame.old frame.registered frame.packetAt (frame.depth+offset+1)))
   (SourceNativeTemporalVisitAt.finite
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+offset+1)).state.down))
 rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime_depth]
 exact heq_of_eq (congrArg SourceNativeTemporalVisitAt.finite (generic_full_visits frame _))

private theorem trace_of_state_eq
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 {environment : Env Value Var} {raw : Expr Value Var ()}
 {first second : SourceOperationExecutionDebt.State environment raw} (same : first=second) :
 HEq first.2 second.2 := by
 cases same
 rfl

private theorem generic_paid_runtime_trace
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (offset : Nat)
 (within : offset ≤ (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1) :
 HEq (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg (0+offset)).event.state.2
 (RS.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
     frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+offset+1))).2.state.2 := by
 rw [generic_paid_prefix_frames frame cfg offset within]
 unfold RS.runtimeCurrent
 rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime_depth]
 exact trace_of_state_eq (congrArg (fun current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered => current.2.state)
   (generic_full_visits frame (frame.depth+offset+1) |> congrArg RootVisit.current))

private theorem stopping_full_runtime_visit
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (generic_paid_runtime_visit (receiverFrame producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (N.receipt producer packet).1 (Nat.le_refl _)) :=
 generic_paid_runtime_visit _ _ _ (Nat.le_refl _)

private theorem stopping_full_runtime_trace
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (generic_paid_runtime_trace (receiverFrame producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (N.receipt producer packet).1 (Nat.le_refl _)) :=
 generic_paid_runtime_trace _ _ _ (Nat.le_refl _)

private theorem actual_native_born_step
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt_next
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (receiverFrame producer packet) 0) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt_next _ _ _

private theorem generic_stop_value
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).2.1.1 =
 frame.rawRead.expression.eval frame.rawRead.environment := by
 have paid := SourceOperationExecutionDebt.completed_value
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.atReceipt cfg frame 0).event.state
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).2.1
 change _ = (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg
   (0+(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1)).rawRead.expression.eval
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames frame cfg
   (0+(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.receipt cfg frame 0).1)).rawRead.environment at paid
 rw [generic_stopping_raw_source] at paid
 exact paid

private theorem native_value_from_actual_input
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 N.nativeValue producer packet =
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1)).eval
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1)).environment :=
 generic_stop_value (receiverFrame producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)

private theorem actual_material_endpoint
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).state.1 =
 .const (SourceGeneratedInquiryReceiptAction.actionResultAt packet.2.1.1 packet.2.2.1
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence packet.2.1.1)).2.2.1 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression _ _ _

private theorem actual_input_residual_effect
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1)).eval
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1)).environment =
 (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).environment
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).increment := by
 rw [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression_eval,actual_material_endpoint]
 simp only [Expr.eval]
 have old := (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).state.2.sound
 rw [actual_material_endpoint] at old
 simp only [Expr.eval] at old
 change (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
   ((SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).environment+
    (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1).increment) - _ = _
 rw [Expr.eval_update,old]
 abel

private theorem stopping_current
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 (N.selected producer packet).currentState.visit.current =
 RS.runtimeCurrent (N.selected producer packet).old.root.toAuthoritativeRoot
   (N.selected producer packet).registered (N.selected producer packet).packetAt
   (SourceRegisteredClaimClock.currentRuntime (N.selected producer packet)) :=
 by
 unfold SourceRegisteredClaimClock.currentRuntime RS.runtimeCurrent
 rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime_depth]
 exact SourceRegisteredClaimClock.source_current (N.selected producer packet) _

private theorem installed_native_raw
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 (RS.rawFace (receiverFrame producer packet).old.root.toAuthoritativeRoot
   (receiverFrame producer packet).registered (receiverFrame producer packet).packetAt
   (SourceRegisteredClaimClock.currentRuntime (receiverFrame producer packet))).rootRead.expression =
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
   (SourceGeneratedInquiryReceiptAction.actualMaterial packet.2.1.1 packet.2.2.1) := by
 change (N.nativePacket producer packet).2.1.1.registered.input.expression = _
 exact N.receiver_ast producer packet

private def runtimeFor
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=())) (offset : Nat) :=
 RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
 frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+offset+1)

private def facadeFor
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
   (Value:=Value) (Var:=Var) (sort:=())) :=
 RS.facade frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- This registered request was emitted from the actual R action material. -/
def receiver := receiverFrame (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)
def configuration := ActualCofinalSourceAction.AS.stockCfg
 (N.nativePacket (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)).2.2.1

def sourceFacade := facadeFor (receiver observation nontrivial half depth ordinal)
def runtimeAt (offset : Nat) := runtimeFor (receiver observation nontrivial half depth ordinal) offset

def frontier := nativeFrontier (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)

theorem realization : SourceNativeRuntimeCalculationRealizationAt
 (frontier observation nontrivial half depth ordinal) :=
 nativeRealization (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)

theorem actual_source_input : type_of% (native_registered_input
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 native_registered_input _ _

theorem actual_source_stage
 (index : Fin ((frontier observation nontrivial half depth ordinal).stageCount+1)) : type_of%
 ((realization observation nontrivial half depth ordinal).operationAt index) :=
 (realization observation nontrivial half depth ordinal).operationAt index

def stoppingOffset := (N.receipt (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)).1

theorem actual_full_prefix (offset : Nat)
 (within : offset ≤ stoppingOffset observation nontrivial half depth ordinal) : type_of%
 (generic_paid_prefix_frames (receiver observation nontrivial half depth ordinal)
 (configuration observation nontrivial half depth ordinal) offset within) :=
 generic_paid_prefix_frames _ _ _ within

theorem actual_full_current : type_of% (stopping_full_runtime_current
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 stopping_full_runtime_current _ _

theorem actual_full_visit : type_of% (stopping_full_runtime_visit
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 stopping_full_runtime_visit _ _

theorem actual_full_trace : type_of% (stopping_full_runtime_trace
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 stopping_full_runtime_trace _ _

theorem actual_native_born : type_of% (actual_native_born_step
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 actual_native_born_step _ _

theorem actual_native_value_effect :
 N.nativeValue (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal) =
 (OriginalKFullSourceRAction.material observation nontrivial half depth ordinal).raw.effect
 (OriginalKFullSourceRAction.material observation nontrivial half depth ordinal).environment
 (OriginalKFullSourceRAction.material observation nontrivial half depth ordinal).increment :=
 (native_value_from_actual_input _ _).trans (actual_input_residual_effect _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeRuntimeFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
