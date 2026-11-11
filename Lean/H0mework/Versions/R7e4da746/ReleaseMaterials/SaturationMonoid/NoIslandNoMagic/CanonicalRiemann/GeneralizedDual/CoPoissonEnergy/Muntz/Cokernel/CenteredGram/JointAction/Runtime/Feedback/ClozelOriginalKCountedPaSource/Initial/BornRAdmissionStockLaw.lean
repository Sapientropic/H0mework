import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRActualHistoryConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRAdmissionStockLaw
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
open private retainedCode from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private packetTransport from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Stage
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory sourceRuntime)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end Lower
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative localNativeReceipt receiver nextBase stockCfg)
end AS
namespace Admissions
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor actual_index historyAt)
end Admissions
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next nextBorn actualOccurrence)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_paid_prefix)
end Prefix
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression)
end N
namespace F
export BornWholeStockRConsumer.Generic (born_expression)
end F
namespace Generic
variable {Sorts:Type} {U X:Sorts→Type} [∀s,AddCommGroup (U s)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
variable (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=U) (PhysicalVar:=X) (sort:=s))
theorem paid_prefix_expression (count:Nat) (within:count≤(S.Complete.receipt cfg frame 0).1) :
 (S.frames frame cfg (0+count)).registered.input.expression=frame.registered.input.expression := by
 induction count with
 | zero=>rfl
 | succ count previous=>
  have paid:=S.Prefix.receipt_paid_prefix cfg frame 0 ⟨count,by omega⟩
  have move:S.frames frame cfg (0+(count+1))=(S.frames frame cfg (0+count)).mathNext := by
   change S.next (S.frames frame cfg (0+count)) cfg=_
   unfold S.next
   rw [paid.2.down]
  exact (congrArg (fun current:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
   (Value:=U) (Var:=X) (sort:=s)=>current.registered.input.expression) move).trans
    (previous (by omega))
end Generic
local instance baseGroups:∀s,AddCommGroup (A.W s):=BornRCanonicalMethodRuntime.levelGroups 0
local instance levelGroups (n:Nat):∀s,AddCommGroup (Lower.Value A.W n s):=
 BornRCanonicalMethodRuntime.levelGroups n
local instance pairGroups (n:Nat):∀s,AddCommGroup (PairValue (Lower.Value A.W n) s):=
 BornRCanonicalMethodRuntime.levelGroups (n+1)
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CountedPaInitial.CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half
local notation "initial"=>H.receiver observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal

private theorem after_native_retained
 (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)) :
 HEq
  (retainedCode (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).1
   (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.1.1)
  (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W packet.1) slot))
   (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W packet.1) slot))
    (R.actualMaterial packet.2.1.1 packet.2.2.1).state.1)) := by
 rcases packet with ⟨n,⟨source,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 cases language
 let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=
  { LowVar:=A.X,datum:=datum,nextInventory:=inventory,nextPairInventory:=pairInventory }
 let native:=AS.receiver factory n (source,seed) cfg rfl
 let base:=AS.nextBase factory n (source,seed) cfg rfl
 let distance:=(S.Complete.receipt (AS.stockCfg base) native 0).1
 let selected:=S.frames native (AS.stockCfg base) (0+distance)
 have oldRegistered:native.registered.input.expression=N.expression (R.actualMaterial source cfg):=rfl
 have keptRegistration: selected.registered.input.expression=native.registered.input.expression:=
  Generic.paid_prefix_expression native (AS.stockCfg base) distance (Nat.le_refl _)
 have born:=F.born_expression selected (AS.stockCfg base)
 have sourceRaw:=born.trans (congrArg
  (fun expr:Expr (PairValue (Lower.Value A.W n)) A.X slot=>Expr.add expr
   (Expr.linear (-AddMonoidHom.id (PairValue (Lower.Value A.W n) slot)) selected.event.state.1))
  (keptRegistration.trans oldRegistered))
 dsimp only [cfg,native,base,distance,selected,A.X,CompletedSourceRCalculation.Var] at sourceRaw
 dsimp only [AS.nativeAfterAdmission,AS.bornAfterNative,AS.localNativeReceipt,packetTransport,id]
 unfold retainedCode
 rw [sourceRaw]
 rfl

theorem actual_successor_retained (update:Nat) :
 HEq
  (retainedCode (Admissions.packetAt factory initial pR rfl (update+1)).1
   (Admissions.packetAt factory initial pR rfl (update+1)).2.1.1)
  (Expr.linear (-AddMonoidHom.id
   (PairValue (Lower.Value A.W (Admissions.packetAt factory initial pR rfl update).1) slot))
   (Expr.linear (-AddMonoidHom.id
    (PairValue (Lower.Value A.W (Admissions.packetAt factory initial pR rfl update).1) slot))
    (R.actualMaterial (Admissions.packetAt factory initial pR rfl update).2.1.1
     (Admissions.packetAt factory initial pR rfl update).2.2.1).state.1)) := by
 rw [Admissions.packetAt_successor]
 exact after_native_retained observation nontrivial half (Admissions.packetAt factory initial pR rfl update)

def actual_source_step (update:Nat) :=
 PProd.mk (Admissions.actual_index factory initial pR rfl update) <|
 PProd.mk (Admissions.historyAt factory initial pR rfl update)
 (actual_successor_retained observation nontrivial half depth ordinal update)
end CountedPaInitial.BornRAdmissionStockLaw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
