import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSealedMethodHistory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
open CenteredGram.IntegralGraphJointAction
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory nativeStock nativePaComponent nativeSourceComponent nativeWordComponent nativeGammaCotestComponent)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value)
end Lower
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Packet)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative nextCfg nextBase stockCfg)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions (packetAt packetAt_successor)
end D
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base baseRoot actualVisit actualOccurrence)
end S
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (stockLaw component)
end I
namespace Affine
export SourceFamilyCurrentAffineWrite (component combined)
end Affine
local instance levelGroups (n:Nat):∀t,AddCommGroup (Lower.Value A.W n t):=BornRCanonicalMethodRuntime.levelGroups n
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "slot"=>CompletedSourceRCalculation.Slot.branches
local notation "factory"=>A.fixedRFactory observation nontrivial half

def templateFace (n:Nat) (data:SF.Packet (W:=A.W) (X:=A.X) (s:=slot) n)
 (sourceCfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot))
 (language:sourceCfg.LowVar=A.X)
 (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Lower.Value A.W (n+1)) (Var:=sourceCfg.LowVar) (sort:=slot)) :
 SourceNativeRootSemanticFaceAt (S.baseRoot frame (AS.nextCfg factory n data sourceCfg language))
  (S.actualVisit frame):=by
 cases sourceCfg with
 | mk Y datum inventory pairInventory=>
  change Y=A.X at language
  cases language
  let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=⟨A.X,datum,inventory,pairInventory⟩
  let base:=AS.nextBase factory n data cfg rfl
  let prior:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
   (PhysicalValue:=Lower.Value A.W (n+1)) (PhysicalVar:=A.X) (sort:=slot):=
   {base with datum:=fun current=>{base.datum current with
     component:=some (A.nativeSourceComponent observation nontrivial half (n+1) current)}}
  let actual:=AS.stockCfg base
  let epoch:=SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame
  let native:=A.nativePaComponent observation nontrivial half (n+1) epoch
  let nativeBase:={(S.base epoch).root.source.base with projectionLaw:=native}
  let word:=A.nativeWordComponent observation nontrivial half (n+1) epoch
  let wordBase:=nativeBase.withProjectionCoface word
  let gamma:=A.nativeGammaCotestComponent observation nontrivial half (n+1) epoch
  let combined:=A.nativeSourceComponent observation nontrivial half (n+1) epoch
  let sourceRoot:=(S.base epoch).root.withProjectionCoface combined
  let installed:=(SourceNativeProjectionLaw.InstallationAt.componentCoface wordBase gamma) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base epoch).root.source.base combined) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface sourceRoot.source.base (Affine.component epoch)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    {(S.base epoch).root.source.base with projectionLaw:=Affine.combined epoch prior}
    (I.stockLaw epoch base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base (I.component epoch base))
  exact {projection:=installed.embed PUnit.unit,active:=PUnit.unit,classifier_eq:=rfl}

def templateStock (n:Nat)
 (sourceCfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot))
 (language:sourceCfg.LowVar=A.X)
 (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Lower.Value A.W (n+1)) (Var:=sourceCfg.LowVar) (sort:=slot)):
 CompletedSourceRCalculation.Value slot:=by
 cases sourceCfg with
 | mk Y datum inventory pairInventory=>
  change Y=A.X at language
  cases language
  exact A.nativeStock (n+1) frame

theorem template_source (n:Nat) (data:SF.Packet (W:=A.W) (X:=A.X) (s:=slot) n)
 (sourceCfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot))
 (language:sourceCfg.LowVar=A.X)
 (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Lower.Value A.W (n+1)) (Var:=sourceCfg.LowVar) (sort:=slot)):
 HEq (templateFace observation nontrivial half n data sourceCfg language frame).rootRead
  (actionMaterial observation nontrivial half (templateStock n sourceCfg language frame)):=by
 cases sourceCfg with
 | mk Y datum inventory pairInventory=>
  change Y=A.X at language
  cases language
  rfl

structure Installed (source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)) where
 face:SourceNativeRootSemanticFaceAt (S.baseRoot source.2.1.1 source.2.2.1) (S.actualVisit source.2.1.1)
 source_read:HEq face.rootRead (actionMaterial observation nontrivial half (A.nativeStock source.1 source.2.1.1))

def Installed.read {source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)}
 (installed:Installed observation nontrivial half source):
 ActionMaterial observation nontrivial half (A.nativeStock source.1 source.2.1.1):=
 cast (type_eq_of_heq installed.source_read) installed.face.rootRead

theorem Installed.read_source {source:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)}
 (installed:Installed observation nontrivial half source):
 installed.read=actionMaterial observation nontrivial half (A.nativeStock source.1 source.2.1.1):=by
 exact eq_of_heq ((cast_heq (type_eq_of_heq installed.source_read) installed.face.rootRead).trans installed.source_read)

def afterNativeInstalled (before:AS.AdmissionPacket (W:=A.W) (X:=A.X) (s:=slot)):
 Installed observation nontrivial half (AS.bornAfterNative (AS.nativeAfterAdmission factory before)):=by
 rcases before with ⟨n,⟨frame,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y=A.X at language
 cases language
 let cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=Lower.Value A.W n) (PhysicalVar:=A.X) (sort:=slot):=⟨A.X,datum,inventory,pairInventory⟩
 let next:=AS.bornAfterNative (AS.nativeAfterAdmission factory ⟨n,⟨frame,seed⟩,cfg,⟨rfl⟩⟩)
 exact {
  face:=templateFace observation nontrivial half n (frame,seed) cfg rfl next.2.1.1
  source_read:=template_source observation nontrivial half n (frame,seed) cfg rfl next.2.1.1 }

def actualInstalled (depth ordinal update:Nat):
 Installed observation nontrivial half (D.packetAt factory
  (H.receiver observation nontrivial half depth ordinal) (H.methodProgramme observation nontrivial half depth ordinal) rfl (update+1)):=
 (congrArg (Installed observation nontrivial half)
  (D.packetAt_successor factory (H.receiver observation nontrivial half depth ordinal)
   (H.methodProgramme observation nontrivial half depth ordinal) rfl update)).mpr
  (afterNativeInstalled observation nontrivial half
   (D.packetAt factory (H.receiver observation nontrivial half depth ordinal)
    (H.methodProgramme observation nontrivial half depth ordinal) rfl update))

end CountedPaInitial.BornRNativeGammaInstall
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
