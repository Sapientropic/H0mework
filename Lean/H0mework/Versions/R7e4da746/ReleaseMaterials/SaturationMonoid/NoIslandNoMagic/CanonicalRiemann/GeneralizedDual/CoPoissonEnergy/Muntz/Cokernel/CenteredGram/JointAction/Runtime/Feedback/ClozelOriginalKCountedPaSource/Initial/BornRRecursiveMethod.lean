import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourceMethodConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRRecursiveMethod
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace C
export CompletedSourceRCalculation (Value Var)
end C
namespace F
export BornWholeStockRConsumer (registeredValue actual_registered_next)
end F
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (query actualOccurrence resultFace baseRoot runtime)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader actionResultAt)
end R
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme result_value)
end Q
namespace Configured
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end Configured
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
 (generatedAction compiles successor_valid target_next)
end Intake
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value)
end OF
namespace NextMethod
variable {Sorts:Type} {U X:Sorts→Type} [∀s,AddCommGroup (U s)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
variable (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=U) (PhysicalVar:=X) (sort:=s)) (r:U s→+U s)
abbrev material := R.actualMaterial frame cfg
abbrev previous := (R.actionResultAt frame cfg (S.actualOccurrence frame)).2.2.1
/-- The next code reads the actual paid output expression, with its unchanged Trace index. -/
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue U)) (Var:=cfg.LowVar) (sort:=s) :=
 ⟨pairEnvironment (material frame cfg).environment 0,
  .linear ((r.prodMap r).prodMap (r.prodMap r))
   (liftExpr (material frame cfg).state.1)⟩
abbrev receiver := Configured.lowInitial frame cfg
def lowProgramme := { Configured.lowProgramme frame cfg with
 datum:=fun current=>{ (Configured.lowProgramme frame cfg).datum current with
  calculationReader:=some (fun {_current} _supplied=>raw frame cfg r) } }
def programme := Q.programme (lowProgramme frame cfg r)
abbrev admitted := Intake.generatedAction frame cfg (programme frame cfg r)
theorem reader_actual_source :
 (S.query (receiver frame cfg) (programme frame cfg r)).raw=raw frame cfg r := rfl

theorem previous_paid : (material frame cfg).state.1.eval (material frame cfg).environment=previous frame cfg :=
 (material frame cfg).state.2.sound.symm.trans
 (OF.source_value (S.baseRoot frame cfg).toAuthoritativeRoot
  (R.actionReader frame cfg) (S.actualOccurrence frame)).symm

theorem whole_source :
 (R.actionResultAt (receiver frame cfg) (programme frame cfg r)
  (S.actualOccurrence (receiver frame cfg))).2.2.1=
 ((r.prodMap r) (previous frame cfg),0) := by
 have generated:=OF.source_value
  (S.baseRoot (receiver frame cfg) (programme frame cfg r)).toAuthoritativeRoot
  (R.actionReader (receiver frame cfg) (programme frame cfg r))
  (S.actualOccurrence (receiver frame cfg))
 have lifted:=BornRSourceMethodConsumer.Generic.pair_zero
  (material frame cfg).state.1 (material frame cfg).environment
 have acted:=congrArg ((r.prodMap r).prodMap (r.prodMap r)) lifted
 have evaluated : (raw frame cfg r).expression.eval (raw frame cfg r).environment=
  ((r.prodMap r) (previous frame cfg),0) := by
  exact acted.trans (by
   change ((r.prodMap r) ((material frame cfg).state.1.eval (material frame cfg).environment),
    (r.prodMap r) 0)=_
   rw [previous_paid,map_zero])
 exact generated.trans evaluated

theorem material_source :
 (R.actualMaterial (receiver frame cfg) (programme frame cfg r)).state.1.eval
  (R.actualMaterial (receiver frame cfg) (programme frame cfg r)).environment=
 ((r.prodMap r) ((material frame cfg).state.1.eval (material frame cfg).environment),0) :=
 (previous_paid (receiver frame cfg) (programme frame cfg r)).trans <|
  (whole_source frame cfg r).trans <|
   congrArg (fun value:PairValue U s=>((r.prodMap r) value,0)) (previous_paid frame cfg).symm

theorem compiled : type_of% (Intake.compiles frame cfg (programme frame cfg r)) :=
 Intake.compiles frame cfg (programme frame cfg r)
theorem successor : type_of% (Intake.successor_valid frame cfg (programme frame cfg r)) :=
 Intake.successor_valid frame cfg (programme frame cfg r)
end NextMethod

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CountedPaInitial.CompletedSourceRCalculation.Slot.branches
private def baseAction : C.Value slot→+C.Value slot :=
 (OriginalKFullSourceRAction.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
local notation "baseR"=>baseAction observation nontrivial half

private structure Payload (r0:C.Value slot→+C.Value slot)
 (U X:CountedPaInitial.CompletedSourceRCalculation.Slot→Type) [∀s,AddCommGroup (U s)] where
 frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=U) (Var:=X) (sort:=slot)
 cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=U) (PhysicalVar:=X) (sort:=slot)
 action:U slot→+U slot
 paidRead:PairValue U slot
 paid_source:(R.actualMaterial frame cfg).state.1.eval (R.actualMaterial frame cfg).environment=paidRead
 read:U slot→+C.Value slot
 commutes:∀value,read (action value)=r0 (read value)

private structure Packet (r0:C.Value slot→+C.Value slot) where
 Value:CountedPaInitial.CompletedSourceRCalculation.Slot→Type
 Var:CountedPaInitial.CompletedSourceRCalculation.Slot→Type
 groups:∀s,AddCommGroup (Value s)
 payload:@Payload r0 Value Var groups

private def initialPacket : Packet baseR :=
 { Value:=PairValue C.Value
   Var:=C.Var
   groups:=fun _=>inferInstance
   payload:={ frame:=H.receiver observation nontrivial half depth ordinal
              cfg:=H.methodProgramme observation nontrivial half depth ordinal
              action:=(baseR).prodMap baseR
              paidRead:=(R.actualMaterial (H.receiver observation nontrivial half depth ordinal)
               (H.methodProgramme observation nontrivial half depth ordinal)).state.1.eval
               (R.actualMaterial (H.receiver observation nontrivial half depth ordinal)
                (H.methodProgramme observation nontrivial half depth ordinal)).environment
              paid_source:=rfl
              read:=AddMonoidHom.fst _ _
              commutes:=fun _=>rfl } }

private def nextPacket {r0:C.Value slot→+C.Value slot} (packet:Packet r0) : Packet r0 := by
 letI := packet.groups
 exact { Value:=PairValue packet.Value
         Var:=packet.payload.cfg.LowVar
         groups:=fun _=>inferInstance
         payload:={ frame:=NextMethod.receiver packet.payload.frame packet.payload.cfg
                    cfg:=NextMethod.programme packet.payload.frame packet.payload.cfg packet.payload.action
                    action:=packet.payload.action.prodMap packet.payload.action
                    paidRead:=((packet.payload.action.prodMap packet.payload.action) packet.payload.paidRead,0)
                    paid_source:=(NextMethod.material_source packet.payload.frame packet.payload.cfg packet.payload.action).trans
                     (congrArg (fun value:PairValue packet.Value slot=>
                      ((packet.payload.action.prodMap packet.payload.action) value,0)) packet.payload.paid_source)
                    read:=packet.payload.read.comp (AddMonoidHom.fst _ _)
                    commutes:=fun value=>packet.payload.commutes value.1 } }

private def stock {r0:C.Value slot→+C.Value slot} (packet:Packet r0) : C.Value slot := by
 letI := packet.groups
 exact packet.payload.read packet.payload.paidRead.1

private theorem next_stock {r0:C.Value slot→+C.Value slot} (packet:Packet r0) :
 stock (nextPacket packet)=r0 (stock packet) := by
 let _ := packet.groups
 exact packet.payload.commutes packet.payload.paidRead.1

private def nextTree {r0:C.Value slot→+C.Value slot} (packet:Packet r0) : RootedAccountedUnfolding (Packet r0) :=
 RootedAccountedUnfolding.zero (nextPacket packet)

private def materialHistory (fuel:Nat) : RootedAccountedUnfolding (Packet baseR) :=
 (RootedAccountedUnfolding.advance nextTree)^[fuel]
  (RootedAccountedUnfolding.zero (initialPacket observation nontrivial half depth ordinal))

def actual_material_history (fuel:Nat) :=
 PProd.mk (F.actual_registered_next observation nontrivial half depth ordinal)
  (materialHistory observation nontrivial half depth ordinal fuel)
end CountedPaInitial.BornRRecursiveMethod
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
