import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Completion
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace SourceRegisteredClaimClock
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (finiteVisit mathCurrent mathState)
end J
namespace R
export RootGeneratedDebtActivationJointSource.Successor.Restructuring (finiteVisit runtimeCurrent)
end R
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
  (runtime runtime_depth event budget completedRuntime completedEvent completed completed_budget)
end C
namespace K
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current targetCurrent)
end K
variable {S : Type u} {U X : S → Type u} [∀t,AddCommGroup (U t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=U) (Var:=X) (sort:=s))

theorem source_current (count : Nat) :
    (J.finiteVisit frame.old frame.registered frame.packetAt count).current =
      (R.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).current := by
  induction count with
  | zero => rfl
  | succ count previous =>
    change K.targetCurrent frame.registered frame.packetAt
      (J.finiteVisit frame.old frame.registered frame.packetAt count).current =
      K.targetCurrent frame.registered frame.packetAt
      (R.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).current
    exact congrArg (K.targetCurrent frame.registered frame.packetAt) previous

theorem current_event : frame.event.state =
    (C.event frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)).state := by
  have depth := C.runtime_depth frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)
  change (J.finiteVisit frame.old frame.registered frame.packetAt (frame.depth+1)).current.2.state =
    (R.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
      (C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1))).2.state
  rw [R.runtimeCurrent,depth]
  exact congrArg (fun current : K.Current frame.registered => current.2.state) (source_current frame (frame.depth+1))

def currentRuntime := C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)
def sourceRemainder := remaining frame.event.state.1
def sourceBudget := remaining frame.registered.input.expression

theorem remainder_generated : sourceRemainder frame = sourceBudget frame-(frame.depth+1) :=
  (congrArg (fun state => remaining state.1) (current_event frame)).trans
    (C.budget frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1))

theorem runtime_advance (first steps : Nat) :
    (C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt first).advance steps =
      C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (first+steps) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    change ((C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt first).advance steps).tick.next = _
    rw [previous]
    rfl

def suffixHistory := SourceGeneratedRuntimeMaterialHistoryAt.generate (currentRuntime frame) (sourceRemainder frame)

theorem suffix_ends_at_original
    (paid : 0 < sourceRemainder frame) :
    (suffixHistory frame).target = C.completedRuntime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt := by
  have budget := remainder_generated frame
  have clock : frame.depth+1+sourceRemainder frame=sourceBudget frame := by omega
  change (currentRuntime frame).advance (sourceRemainder frame) = _
  rw [currentRuntime,runtime_advance,clock]
  rfl

theorem suffix_no_restart
    (paid : 0 < sourceRemainder frame) :
    (R.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
      (suffixHistory frame).target).2.state =
      (C.completedEvent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt).state := by
  rw [suffix_ends_at_original frame paid]
  rfl

theorem source_suffix_factorizes : type_of% (SourceGeneratedRuntimeMaterialHistoryAt.target_factorizes (suffixHistory frame)) :=
  SourceGeneratedRuntimeMaterialHistoryAt.target_factorizes (suffixHistory frame)

end SourceRegisteredClaimClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
