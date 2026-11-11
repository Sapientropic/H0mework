import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Whole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
local instance materialGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
namespace Pay
export OriginalKSourceFeedbackSuccessorAction.Pay (BornWholeWrite bornWholeWrite)
end Pay
namespace ST
export OriginalKSourceFeedbackSuccessorAction.ST (birthProgram target_root target_current)
end ST
namespace SO
export OriginalKSourceFeedbackSuccessorAction.SO (root current visit)
end SO
namespace AN
export ActualNativeRelationTransport (paid)
end AN
namespace NativeRequest
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression expression_eval)
end NativeRequest

private theorem material_endpoint_and_effect
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (value : Value ()) (endpoint : (AN.paid frame).state.1=.const value) :
 value+(AN.paid frame).raw.effect (AN.paid frame).environment (AN.paid frame).increment=
 (AN.paid frame).raw.eval ((AN.paid frame).environment+(AN.paid frame).increment) := by
 have source := (AN.paid frame).state.2.sound
 rw [endpoint] at source
 simp only [Expr.eval] at source
 rw [Expr.eval_update,source]

private theorem actual_selected_material_endpoint
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (base : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).state.1=
  .const ((Complete.receipt (AS.stockCfg base) initial 0).2.1.1) :=
 (Complete.receipt (AS.stockCfg base) initial 0).2.1.2.down

private theorem actual_selected_material_update
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (base : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 (Complete.receipt (AS.stockCfg base) initial 0).2.1.1+
  (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).raw.effect
   (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).environment
   (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).increment=
 (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).raw.eval
  ((AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).environment+
   (AN.paid (Complete.atReceipt (AS.stockCfg base) initial 0)).increment) :=
 material_endpoint_and_effect _ _ (actual_selected_material_endpoint base initial)

private theorem material_registered_update
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (value registeredValue : Value ())
 (endpoint : (AN.paid frame).state.1=.const value)
 (generated : registeredValue=(AN.paid frame).raw.effect (AN.paid frame).environment (AN.paid frame).increment) :
 value+registeredValue=(AN.paid frame).raw.eval ((AN.paid frame).environment+(AN.paid frame).increment) := by
 rw [generated]
 exact material_endpoint_and_effect frame value endpoint

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance materialBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance materialNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

/-- This same whole's registered source residual is read from its native material, separately from its decoder-written raw state. -/
def continuationWholeRegisteredValue :=
 (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
  (continuationSourceBorn t factory packet).registered.input.expression.eval
   (continuationSourceBorn t factory packet).registered.input.environment)

/-- The source-generated paid material keeps its actual before environment, increment and raw effect. -/
def continuationMaterialEffect :=
 (AN.paid (continuationSourceSelected t factory packet)).raw.effect
  (AN.paid (continuationSourceSelected t factory packet)).environment
  (AN.paid (continuationSourceSelected t factory packet)).increment

/-- The existing whole environment/expression consumer generates this equality from the actual receipt endpoint and paid trace. -/
theorem continuation_whole_registered_material_effect :
 continuationWholeRegisteredValue t factory packet=continuationMaterialEffect t factory packet := by
 have endpoint := actual_selected_material_endpoint (continuationSourceStockEmitter t factory packet)
  (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
   (actualCurrentSourceBase t factory packet) rfl)
 exact OriginalKMaterialPhysicalStockSourceAction.whole_registered_native_effect
  (continuationSourceSelected t factory packet) (continuationSourceStockEmitter t factory packet)
  (continuationActualWhole t factory packet) _ endpoint

/-- The actual material update is generated by its source increment; its receipt endpoint and registered residual are both retained. -/
theorem continuation_material_actual_update :
 (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
  (continuationSourceReceipt t factory packet).2.1.1)+continuationWholeRegisteredValue t factory packet=
 (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
  (AN.paid (continuationSourceSelected t factory packet)).raw.eval
   ((AN.paid (continuationSourceSelected t factory packet)).environment+
    (AN.paid (continuationSourceSelected t factory packet)).increment)) := by
 exact material_registered_update (continuationSourceSelected t factory packet)
  (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
   (continuationSourceReceipt t factory packet).2.1.1)
  (continuationWholeRegisteredValue t factory packet)
  (actual_selected_material_endpoint (continuationSourceStockEmitter t factory packet)
   (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
    (actualCurrentSourceBase t factory packet) rfl))
  (continuation_whole_registered_material_effect t factory packet)

/-- This read is recovered from the actual whole's source update and registered residual, rather than a freely supplied after-value. -/
def continuationWholeMaterialInput : PairValue
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () :=
 WB.oldPaid (actualCurrentSourceData t factory packet).1 (actualCurrentSourceBase t factory packet)+
 ((show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
   (AN.paid (continuationSourceSelected t factory packet)).raw.eval
    ((AN.paid (continuationSourceSelected t factory packet)).environment+
     (AN.paid (continuationSourceSelected t factory packet)).increment))-
  continuationWholeRegisteredValue t factory packet)

/-- The source AST, trace and complete increment recover precisely this same decoder's actual native input. -/
theorem continuation_whole_material_input_receipt :
 continuationWholeMaterialInput t factory packet=continuationSourceUpdatedTotal t factory packet := by
 unfold continuationWholeMaterialInput
 rw [←continuation_material_actual_update,add_sub_cancel_right]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
