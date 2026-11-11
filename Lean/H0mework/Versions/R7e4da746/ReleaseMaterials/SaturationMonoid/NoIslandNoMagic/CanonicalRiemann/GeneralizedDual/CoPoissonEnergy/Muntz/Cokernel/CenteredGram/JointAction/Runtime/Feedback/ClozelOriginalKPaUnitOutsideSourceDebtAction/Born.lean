import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Emitter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn)
end Shared
namespace Environment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end Environment
namespace CF
export OriginalKFullSourceRAction.CF (collapseValue code_base_value)
end CF
namespace Pay
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (nativeEventValue)
end Pay

private theorem receipt_native_value {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 Pay.nativeEventValue (Complete.atReceipt cfg initial 0).event = (Complete.receipt cfg initial 0).2.1.1 := by
 have actual := (Complete.receipt cfg initial 0).2.2.2
 change RootGeneratedDebtActivationJointSource.mathAction (Complete.atReceipt cfg initial 0).event = Sum.inl (Complete.receipt cfg initial 0).2.1 at actual
 unfold Pay.nativeEventValue
 rw [actual]

private theorem eval_language_transport {Y Z : Unit → Type} (same : Y=Z)
 {Value : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (code : Expr Value Z ()) (environment : Env Value Y) :
 (same.symm ▸ code : Expr Value Y ()).eval environment = code.eval (same ▸ environment : Env Value Z) := by
 cases same
 rfl

local instance bornSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def actorCfg := AS.stockCfg (sourceEmitterBase source shift factory grade data sourceCfg language)
def actorReceipt := Complete.receipt (actorCfg source shift factory grade data sourceCfg language)
 (AS.receiver factory grade data sourceCfg language) 0
def actorSelected := Complete.atReceipt (actorCfg source shift factory grade data sourceCfg language)
 (AS.receiver factory grade data sourceCfg language) 0
def actorBorn := Shared.nextBorn (actorSelected source shift factory grade data sourceCfg language)
 (actorCfg source shift factory grade data sourceCfg language)
def updatedSourceTotal : PairValue (L.Value (PairValue C.Value) grade) () := WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from
  (actorReceipt source shift factory grade data sourceCfg language).2.1.1)

/-- The installed source decoder is executed by this actual receipt and born occurrence. -/
theorem actual_actor_born_environment : Environment.At
 (actorBorn source shift factory grade data sourceCfg language)
 (sourceActorWrite source shift factory grade data sourceCfg language
  (updatedSourceTotal source shift factory grade data sourceCfg language)) := by
 intro current occurrence
 change sourceActorWrite source shift factory grade data sourceCfg language
  (WB.oldPaid data.1 sourceCfg + (show PairValue (L.Value (PairValue C.Value) grade) () from Pay.nativeEventValue
   (actorSelected source shift factory grade data sourceCfg language).event)) = _
 have value : Pay.nativeEventValue (actorSelected source shift factory grade data sourceCfg language).event =
  (actorReceipt source shift factory grade data sourceCfg language).2.1.1 := receipt_native_value _ _
 exact congrArg (fun value => sourceActorWrite source shift factory grade data sourceCfg language
  (WB.oldPaid data.1 sourceCfg+value)) value

theorem actual_actor_active_environment :
 (actorBorn source shift factory grade data sourceCfg language).activeEnvironment =
 sourceActorWrite source shift factory grade data sourceCfg language
  (updatedSourceTotal source shift factory grade data sourceCfg language) :=
 Environment.active (actual_actor_born_environment source shift factory grade data sourceCfg language)

theorem actual_actor_write_split_increment (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (sourceActorWrite source shift factory grade data sourceCfg language value () name) =
 CF.collapseValue grade value + (splitAction shift source-splitAction 0 source) := by
 unfold sourceActorWrite
 dsimp only
 rw [eval_language_transport language]
 rw [CF.code_base_value]
 change (CF.collapseValue grade ((language ▸ AS.write factory grade data sourceCfg language value) () ())+
  (splitAction shift source + -(splitAction 0 source))) = _
 rw [← sub_eq_add_neg]
 congr 1
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  simp only [AS.write,dite_true]

theorem actual_born_split_increment (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((actorBorn source shift factory grade data sourceCfg language).activeEnvironment () name)-
 CF.collapseValue grade (updatedSourceTotal source shift factory grade data sourceCfg language) =
 (splitAction shift source-splitAction 0 source) := by
 rw [actual_actor_active_environment,actual_actor_write_split_increment]
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
