import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Feedback
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Replay.Packet
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (installation material)
namespace E
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.Elimination
 (fourFaces dual_readback)
end E
end Faces
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance packetGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t,X t → Expr W X t) (n : Nat)
variable (seed : Seed W X s n) (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
abbrev nativeCfg := Future.Replay.Installed.programme (Future.Replay.Binding.at originalBinding n) seed
abbrev actualCfg := cfg (factory (s:=s) originalBinding) n seed

def face : SourceNativeRootSemanticFaceAt (StockObservation.root frame (actualCfg originalBinding n seed))
 (StockObservation.visit frame (actualCfg originalBinding n seed)) where
 projection:=(Faces.installation frame (nativeCfg originalBinding n seed)).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl

theorem actual_material : (face originalBinding n seed frame).rootRead=
 Faces.material (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (nativeCfg originalBinding n seed)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) := rfl

def faces := Faces.E.fourFaces (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
 (nativeCfg originalBinding n seed) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)
 (face originalBinding n seed frame).rootRead

theorem dual_readback : type_of% (Faces.E.dual_readback
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (nativeCfg originalBinding n seed)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)
 (face originalBinding n seed frame).rootRead) := Faces.E.dual_readback _ _ _ _
end Lower.SourceFamily.Replay.Packet
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
