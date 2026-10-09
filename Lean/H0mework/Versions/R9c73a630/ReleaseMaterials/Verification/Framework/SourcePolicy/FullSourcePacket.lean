import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP118FullSourcePacketControls
open RootInquiryCompletion
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission nativeAfterAdmission_grade bornAfterNative
  admissionPoint_successor admissionPoint_successor_grade admissionPoint admissionDistance
  localNativeReceipt stockCfg)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor packetAt_successor_grade index actual_index historyAt
  history_end_index complete_word actual_source_action strictMono cofinal)
end D
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames nextBorn)
end S
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance nativeGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
example : (AS.nativeAfterAdmission factory packet).1 = packet.1+1 := AS.nativeAfterAdmission_grade factory packet
example : (AS.bornAfterNative packet).1 = packet.1 := rfl
example : (AS.bornAfterNative packet).2.1.1 =
 S.nextBorn (S.frames packet.2.1.1 (AS.stockCfg packet.2.2.1) (0+(AS.localNativeReceipt packet).1))
  (AS.stockCfg packet.2.2.1) := rfl
example (start : Nat) : AS.admissionPoint factory initial cfg language
 (start+AS.admissionDistance factory initial cfg language start+1) =
 AS.bornAfterNative (AS.nativeAfterAdmission factory (AS.admissionPoint factory initial cfg language start)) :=
 AS.admissionPoint_successor factory initial cfg language start
example (start : Nat) : (AS.admissionPoint factory initial cfg language
 (start+AS.admissionDistance factory initial cfg language start+1)).1 =
 (AS.admissionPoint factory initial cfg language start).1+1 :=
 AS.admissionPoint_successor_grade factory initial cfg language start
example (ordinal : Nat) : D.packetAt factory initial cfg language (ordinal+1) =
 AS.bornAfterNative (AS.nativeAfterAdmission factory (D.packetAt factory initial cfg language ordinal)) :=
 D.packetAt_successor factory initial cfg language ordinal
example (ordinal : Nat) : (D.packetAt factory initial cfg language (ordinal+1)).1 =
 (D.packetAt factory initial cfg language ordinal).1+1 :=
 D.packetAt_successor_grade factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (D.actual_index factory initial cfg language (ordinal+1)) :=
 D.actual_index factory initial cfg language (ordinal+1)
example (ordinal : Nat) : type_of% (D.history_end_index factory initial cfg language ordinal) :=
 D.history_end_index factory initial cfg language ordinal
example (ordinal : Nat) : type_of% (D.complete_word factory initial cfg language (ordinal+1)) :=
 D.complete_word factory initial cfg language (ordinal+1)
example (ordinal : Nat) : type_of% (D.actual_source_action factory initial cfg language
 (D.index factory initial cfg language ordinal)) :=
 D.actual_source_action factory initial cfg language (D.index factory initial cfg language ordinal)
example : type_of% (D.strictMono factory initial cfg language) := D.strictMono factory initial cfg language
example : type_of% (D.cofinal factory initial cfg language) := D.cofinal factory initial cfg language
example {Result : Sort v} (ordinal : Nat)
 (consume : (next : AS.AdmissionPacket (W := W) (X := X) (s := s)) →
  next = AS.bornAfterNative (AS.nativeAfterAdmission factory
   (D.packetAt factory initial cfg language ordinal)) → Result) : Result :=
 consume (D.packetAt factory initial cfg language (ordinal+1))
  (D.packetAt_successor factory initial cfg language ordinal)
#print axioms AS.bornAfterNative
#print axioms AS.nativeAfterAdmission
#print axioms AS.nativeAfterAdmission_grade
#print axioms AS.admissionPoint_successor
#print axioms AS.admissionPoint_successor_grade
#print axioms D.packetAt_successor
#print axioms D.packetAt_successor_grade
end CP118FullSourcePacketControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
