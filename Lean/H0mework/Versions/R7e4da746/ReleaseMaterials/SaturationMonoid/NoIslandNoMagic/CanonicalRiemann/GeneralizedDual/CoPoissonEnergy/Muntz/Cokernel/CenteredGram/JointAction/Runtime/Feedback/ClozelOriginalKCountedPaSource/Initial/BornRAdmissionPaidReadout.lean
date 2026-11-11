import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRAdmissionStockLaw
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRAdmissionPaidReadout
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
open private retainedCode from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
open private after_native_retained from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRAdmissionStockLaw
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
 (AdmissionPacket nativeAfterAdmission bornAfterNative localNativeReceipt)
end AS
namespace Admissions
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor actual_index historyAt)
end Admissions
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt)
end R
local instance baseGroups:∀s,AddCommGroup (A.W s):=BornRCanonicalMethodRuntime.levelGroups 0
local instance levelGroups (n:Nat):∀s,AddCommGroup (Lower.Value A.W n s):=BornRCanonicalMethodRuntime.levelGroups n
local instance pairGroups (n:Nat):∀s,AddCommGroup (PairValue (Lower.Value A.W n) s):=BornRCanonicalMethodRuntime.levelGroups (n+1)
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CountedPaInitial.CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half
local notation "initial"=>H.receiver observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal

private def retainedValue (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)) :=
 (retainedCode packet.1 packet.2.1.1).eval packet.2.1.1.registered.input.environment

private theorem after_native_value
 (packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)) :
 HEq (retainedValue (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)))
  (R.actionResultAt packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1)).2.2.1 := by
 have sourceAst:=after_native_retained observation nontrivial half packet
 rcases packet with ⟨n,⟨source,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 cases language
 let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=
  {LowVar:=A.X,datum:=datum,nextInventory:=inventory,nextPairInventory:=pairInventory}
 let packet:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot):=⟨n,⟨source,seed⟩,cfg,⟨rfl⟩⟩
 let next:=AS.bornAfterNative (AS.nativeAfterAdmission factory packet)
 let env:=next.2.1.1.registered.input.environment
 have astEq:=eq_of_heq sourceAst
 have read:=congrArg (fun expr:Expr (PairValue (Lower.Value A.W n)) A.X slot=>expr.eval env) astEq
 have normal:=BornRActualHistoryConsumer.Generic.paid_expression source cfg
 have constantRead:=congrArg (fun expr:Expr (PairValue (Lower.Value A.W n)) A.X slot=>expr.eval env) normal
 have paidRead:=BornRSourceMethodConsumer.Generic.negate_paid (R.actualMaterial source cfg).state.1 env
 dsimp only [retainedValue,AS.nativeAfterAdmission,AS.bornAfterNative,AS.localNativeReceipt,packetTransport,id]
 exact heq_of_eq (read.trans (paidRead.trans constantRead))

theorem actual_successor_paid (update:Nat) :
 HEq
  (retainedValue (Admissions.packetAt factory initial pR rfl (update+1)))
  (R.actionResultAt (Admissions.packetAt factory initial pR rfl update).2.1.1
   (Admissions.packetAt factory initial pR rfl update).2.2.1
   (S.actualOccurrence (Admissions.packetAt factory initial pR rfl update).2.1.1)).2.2.1 := by
 rw [Admissions.packetAt_successor]
 exact after_native_value observation nontrivial half (Admissions.packetAt factory initial pR rfl update)

def actual_paid_source_step (update:Nat) :=
 PProd.mk (Admissions.actual_index factory initial pR rfl update) <|
 PProd.mk (Admissions.historyAt factory initial pR rfl update)
 (actual_successor_paid observation nontrivial half depth ordinal update)
end CountedPaInitial.BornRAdmissionPaidReadout
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
