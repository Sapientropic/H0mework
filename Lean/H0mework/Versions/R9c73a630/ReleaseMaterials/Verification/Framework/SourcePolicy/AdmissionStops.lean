import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyActualAdmissionStops
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory actual_whole actual_query actual_receipt actual_branch_receipt actual_node)
end SF
namespace P
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (sourceRuntime receipt distance packet history tickReceipts actual_admission actual_segment history_whole index startAt
  strictMono cover cofinal packetAt actual_index historyAt history_end_index complete_word word_action actual_source_action)
end P
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket localNativeReceipt localPaidAt stockCfg nativePresentation admissionSegment nextAdmissionAt)
end AS
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (state compiles_paid compiles_settled face consumer birthProgram)
end ST
namespace Steps
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames)
end Steps
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)] {sort : Sorts}
local instance stageGroups (n : Nat) (target : Sorts) : AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value Value n target) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.groups Value n target
variable (factory : SF.Factory Value Var sort)
variable (initial : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (language : cfg.LowVar = Var)

example (start : Nat) : type_of% (P.receipt factory initial cfg language start) := P.receipt _ _ _ _ _
example (start : Nat) : type_of% (P.actual_admission factory initial cfg language start) := P.actual_admission _ _ _ _ _
example (start : Nat) : type_of% (P.actual_segment factory initial cfg language start) := P.actual_segment _ _ _ _ _
example (start : Nat) : SourceNativeInquiryRuntime.HistoryAt (P.sourceRuntime factory initial cfg language)
 (P.distance factory initial cfg language start) ((P.sourceRuntime factory initial cfg language).stateAt start) :=
 P.history factory initial cfg language start
example (start fuel : Nat) : SourceNativeInquiryRuntime.runFrom (runtime := P.sourceRuntime factory initial cfg language)
 (fuel+1) ((P.sourceRuntime factory initial cfg language).stateAt start) =
 .step ((P.sourceRuntime factory initial cfg language).tickAt start)
 (SourceNativeInquiryRuntime.runFrom fuel ((P.sourceRuntime factory initial cfg language).stateAt (start+1))) := rfl
example (start : Nat) (offset : Fin (P.distance factory initial cfg language start)) :
 type_of% (P.tickReceipts factory initial cfg language start offset) := P.tickReceipts _ _ _ _ _ _
example (start offset : Nat) : type_of% (P.history_whole factory initial cfg language start offset) :=
 P.history_whole _ _ _ _ _ _
example : StrictMono (P.index factory initial cfg language) := P.strictMono _ _ _ _
example (bound : Nat) : Σ ordinal : Nat,PLift (bound ≤ P.index factory initial cfg language ordinal) :=
 P.cover _ _ _ _ _
example : Filter.Tendsto (P.index factory initial cfg language) Filter.atTop Filter.atTop := P.cofinal _ _ _ _
example (ordinal : Nat) : type_of% (P.actual_index factory initial cfg language ordinal) := P.actual_index _ _ _ _ _
example (ordinal : Nat) : SourceNativeInquiryRuntime.HistoryAt (P.sourceRuntime factory initial cfg language)
 (1+P.distance factory initial cfg language (P.index factory initial cfg language ordinal+1))
 ((P.sourceRuntime factory initial cfg language).stateAt (P.index factory initial cfg language ordinal)) :=
 P.historyAt factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (P.history_end_index factory initial cfg language ordinal) :=
 P.history_end_index _ _ _ _ _
example (ordinal : Nat) : type_of% (P.complete_word factory initial cfg language ordinal) := P.complete_word _ _ _ _ _
example (tick : Nat) : type_of% (P.word_action factory initial cfg language tick) := P.word_action _ _ _ _ _
example (tick : Nat) : type_of% (P.actual_source_action factory initial cfg language tick) := P.actual_source_action _ _ _ _ _

theorem paid_compilation (native : AS.AdmissionPacket (W := Value) (X := Var) (s := sort))
 (offset : Fin (AS.localNativeReceipt native).1) : type_of%
 (ST.compiles_paid (Steps.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0+offset.val))
  (AS.stockCfg native.2.2.1) (AS.localPaidAt native offset).1 (AS.localPaidAt native offset).2.down) :=
 ST.compiles_paid _ _ _ (AS.localPaidAt native offset).2.down

private theorem paid_not_left (grade : Nat)
 (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value Value grade) (Var := Var) (sort := sort))
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state)
 (actual : frame.action = .inr paid)
 (settled : SourceOperationExecutionDebt.Settlement frame.event.state) : frame.action ≠ .inl settled := by
 rw [actual]
 intro impossible
 cases impossible

/-- The actual paid witness cannot be read as settlement. -/
theorem paid_not_settled (native : AS.AdmissionPacket (W := Value) (X := Var) (s := sort))
 (offset : Fin (AS.localNativeReceipt native).1)
 (settled : SourceOperationExecutionDebt.Settlement
  (Steps.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0+offset.val)).event.state) :
 (Steps.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0+offset.val)).action ≠ .inl settled :=
 paid_not_left native.1 _ (AS.localPaidAt native offset).1 (AS.localPaidAt native offset).2.down settled

theorem settled_compilation (native : AS.AdmissionPacket (W := Value) (X := Var) (s := sort)) : type_of%
 (ST.compiles_settled (Steps.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0+(AS.localNativeReceipt native).1))
  (AS.stockCfg native.2.2.1) (AS.localNativeReceipt native).2.1 (AS.localNativeReceipt native).2.2.2) :=
 ST.compiles_settled _ _ _ (AS.localNativeReceipt native).2.2.2

attribute [local irreducible] P.actual_segment AS.nextAdmissionAt


example : P.index factory initial cfg language 0 < P.index factory initial cfg language 1 :=
 P.strictMono factory initial cfg language (a := 0) (b := 1) (Nat.zero_lt_succ 0)

namespace NamedOriginalK
namespace D
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
 (factory data configuration source_whole source_next)
end D
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate = -2*(n+1)) (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.code
example (start : Nat) : type_of% (P.actual_admission D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl) start) := P.actual_admission _ _ _ _ _
example (ordinal : Nat) : type_of% (P.actual_index D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl) ordinal) := P.actual_index _ _ _ _ _
example (ordinal : Nat) : type_of% (P.complete_word D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl) ordinal) := P.complete_word _ _ _ _ _
example : type_of% (P.cover D.factory (D.data observation nontrivial depth half).1
 (D.configuration observation nontrivial half) (by rfl) depth) := P.cover _ _ _ _ _
example : type_of% (D.source_whole observation nontrivial depth half) := D.source_whole _ _ _ _
example : type_of% (D.source_next observation nontrivial depth half) := D.source_next _ _ _ _
end NamedOriginalK

#print axioms AS.nextAdmissionAt
#print axioms P.actual_admission
#print axioms P.actual_segment
#print axioms P.strictMono
#print axioms P.cofinal
#print axioms P.actual_index
#print axioms P.complete_word
#print axioms paid_compilation
#print axioms paid_not_settled
#print axioms settled_compilation
end SourcePolicyActualAdmissionStops
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
