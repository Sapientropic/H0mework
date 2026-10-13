import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyActualCurrentMaterialEnvironmentUpdate
namespace R
export SourceGeneratedInquiryReceiptAction (actionResultAt)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualOccurrence actualVisit)
end S
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance resultGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)
variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (currentFrame : M.Frame (Value := L.Value W (packet.1+1)) (Var := packet.2.2.1.LowVar) (sort := s))
variable {currentFrameCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
variable (atCurrent : I.Occurrence currentFrame (current := currentFrameCurrent))

theorem native_actual_result :
 (R.actionResultAt currentFrame
   (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) atCurrent).2.2.1 =
 (I.materialAt (A.epoch currentFrame) atCurrent).pair := by
 have generated := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (S.baseRoot currentFrame
   (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1)).toAuthoritativeRoot
  (R.actionReader currentFrame
   (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1)) atCurrent
 have own := native_action_raw factory packet currentFrame atCurrent
 exact generated.trans ((congrArg
  (fun source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue (L.Value W (packet.1+1))) (Var := packet.2.2.1.LowVar) (sort := s) =>
     source.expression.eval source.environment) own).trans
  (reader_pair (A.epoch currentFrame) atCurrent))

namespace Native
export ActualCofinalSourceAction (selected)
end Native

structure NativeMaterial where
 frame : M.Frame (Value := L.Value W (packet.1+1))
  (Var := packet.2.2.1.LowVar) (sort := s)
 actual_frame : frame = Native.selected (queryFactory factory) packet
 supplied : I.Occurrence frame (current := (S.actualVisit frame).current)
 actual_occurrence : supplied = S.actualOccurrence frame
 source_ast : (reader (A.epoch frame) supplied).expression = liftExpr (AN.paid frame).raw
 source_environment : (reader (A.epoch frame) supplied).environment =
  pairEnvironment (AN.paid frame).environment (AN.paid frame).increment
 raw : type_of% (native_action_raw factory packet frame supplied)
 value : type_of% (native_actual_result factory packet frame supplied)
 trace : Trace
  (R.actionReader frame (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) supplied).environment
  (R.actionReader frame (AS.stockCfg (Native.nativePacket (queryFactory factory) packet).2.2.1) supplied).expression
  (.const (I.materialAt (A.epoch frame) supplied).pair)
 common : type_of% (native_common_generated factory packet.1 packet.2.1
  packet.2.2.1 packet.2.2.2.down frame)

def nativeMaterial : NativeMaterial factory packet := by
 let frame := Native.selected (queryFactory factory) packet
 let supplied := S.actualOccurrence frame
 have settling := (ActualCofinalSourceAction.receipt (queryFactory factory) packet).2.2.2
 have phase : frame.action.isLeft = true := congrArg Sum.isLeft settling
 exact {
   frame := frame
   actual_frame := rfl
   supplied := supplied
   actual_occurrence := rfl
   source_ast := reader_paid_raw frame supplied
   source_environment := reader_paid_environment frame ((actual_action_isLeft frame).trans phase)
   raw := native_action_raw factory packet frame supplied
   value := native_actual_result factory packet frame supplied
   trace := native_action_trace factory packet frame supplied
   common := native_common_generated factory packet.1 packet.2.1
    packet.2.2.1 packet.2.2.2.down frame }


section ActualConsumer
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions (packetAt)
end D
namespace RC
export ActualCofinalRootResidualConsumer
 (rootedRequest boundaryWord actual_generated_current original_compiles original_whole actual_root_eliminate)
end RC
namespace Future
export ActualCofinalCommonAction (projection actions model_fibre)
export ActualCofinalNativeTower (stageInventory NativeValue)
end Future
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance requestGroups : (t : Sorts) → AddCommGroup
 (Future.NativeValue (queryFactory factory) initial sourceCfg language (ordinal+1) t) :=
 fun t => L.groups W (D.packetAt (queryFactory factory) initial sourceCfg language (ordinal+1)).1 t

abbrev sourcePacket := D.packetAt (queryFactory factory) initial sourceCfg language ordinal

-- The source bundle and request are both generated by this original cofinal packet chain.
def consume_actual {Result : Sort v}
 (consumer : NativeMaterial factory (sourcePacket factory initial sourceCfg language ordinal) →
  (request : type_of% (RC.rootedRequest (queryFactory factory)
   initial sourceCfg language ordinal)) →
  type_of% (RC.actual_generated_current (queryFactory factory) initial sourceCfg language ordinal) →
  Future.projection (queryFactory factory) initial sourceCfg language
   (DFinsupp.single (ordinal+1) (Finsupp.single request.expression 1)) =
  Future.projection (queryFactory factory) initial sourceCfg language
   (DFinsupp.single (ordinal+1) (RC.boundaryWord (queryFactory factory) initial sourceCfg language ordinal)) →
  ((history : List PUnit.{u+1}) → (target : Nat) →
   Future.stageInventory (queryFactory factory) initial sourceCfg language target
    (SourceGeneratedActionWords.run (Future.actions (queryFactory factory) initial sourceCfg language) history
     (DFinsupp.single (ordinal+1) (Finsupp.single request.expression 1))) =
   Future.stageInventory (queryFactory factory) initial sourceCfg language target
    (SourceGeneratedActionWords.run (Future.actions (queryFactory factory) initial sourceCfg language) history
     (DFinsupp.single (ordinal+1) (RC.boundaryWord (queryFactory factory) initial sourceCfg language ordinal)))) →
  type_of% (RC.original_compiles (queryFactory factory) initial sourceCfg language ordinal) →
  type_of% (RC.original_whole (queryFactory factory) initial sourceCfg language ordinal) → Result) : Result :=
 RC.actual_root_eliminate (queryFactory factory) initial sourceCfg language ordinal
  (fun request model compiled whole =>
   consumer (nativeMaterial factory (sourcePacket factory initial sourceCfg language ordinal)) request
    (RC.actual_generated_current (queryFactory factory) initial sourceCfg language ordinal)
    model (fun history target => (Future.model_fibre _ _ _ _ _ _).mp model history target)
    compiled whole)

end ActualConsumer


end SourceFamilyActualCurrentMaterialEnvironmentUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
