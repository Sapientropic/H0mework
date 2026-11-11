import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Complete
export OriginalKMaterialPhysicalStockSourceAction.Complete (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Shared
export OriginalKMaterialPhysicalStockSourceAction.Shared (nextBorn)
end Shared
namespace Environment
export OriginalKMaterialPhysicalStockSourceAction.Environment (At active)
end Environment
namespace Receiver
export OriginalKMaterialPhysicalStockSourceAction.Receiver (receiver)
end Receiver
namespace NativeValue
export OriginalKMaterialPhysicalStockSourceAction.NativeValue (nativeEventValue)
end NativeValue
namespace CF
export OriginalKFullSourceRAction.CF (code_base_value)
end CF
local instance initBornGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem native_receipt_value {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 NativeValue.nativeEventValue (Complete.atReceipt cfg initial 0).event = (Complete.receipt cfg initial 0).2.1.1 := by
 have receipt := (Complete.receipt cfg initial 0).2.2.2
 change RootGeneratedDebtActivationJointSource.mathAction (Complete.atReceipt cfg initial 0).event = Sum.inl (Complete.receipt cfg initial 0).2.1 at receipt
 unfold NativeValue.nativeEventValue
 rw [receipt]

private theorem eval_language {Y Z : Unit → Type} (same : Y=Z)
 {Value : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (code : Expr Value Z ()) (environment : Env Value Y) :
 (same.symm ▸ code : Expr Value Y ()).eval environment = code.eval (same ▸ environment : Env Value Z) := by
 cases same
 rfl

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def sourceInitReceipt := Complete.receipt (AS.stockCfg (sourceSlotInitStockBase t factory grade data sourceCfg language))
 (Receiver.receiver factory grade data sourceCfg language) 0
def sourceInitSelected := Complete.atReceipt (AS.stockCfg (sourceSlotInitStockBase t factory grade data sourceCfg language))
 (Receiver.receiver factory grade data sourceCfg language) 0
def sourceInitBorn := Shared.nextBorn (sourceInitSelected t factory grade data sourceCfg language)
 (AS.stockCfg (sourceSlotInitStockBase t factory grade data sourceCfg language))
def sourceInitUpdatedValue : PairValue (L.Value (PairValue C.Value) grade) () :=
 WB.oldPaid data.1 sourceCfg+(show PairValue (L.Value (PairValue C.Value) grade) () from (sourceInitReceipt t factory grade data sourceCfg language).2.1.1)

theorem source_init_environment : Environment.At (sourceInitBorn t factory grade data sourceCfg language)
 (actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t)
  (sourceInitUpdatedValue t factory grade data sourceCfg language)) := by
 intro current occurrence
 change actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t)
  (WB.oldPaid data.1 sourceCfg+(show PairValue (L.Value (PairValue C.Value) grade) () from NativeValue.nativeEventValue (sourceInitSelected t factory grade data sourceCfg language).event))=_
 exact congrArg (fun value => actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t)
  (WB.oldPaid data.1 sourceCfg+value)) (native_receipt_value _ _)

theorem source_init_active_environment :
 (sourceInitBorn t factory grade data sourceCfg language).activeEnvironment=
 actualSourceSlotWrite factory grade data sourceCfg language (sourceInitCode t)
  (sourceInitUpdatedValue t factory grade data sourceCfg language) :=
 Environment.active (source_init_environment _ _ _ _ _ _)

theorem source_slot_write_read (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (actualSourceSlotWrite factory grade data sourceCfg language code value () name)=
 code.eval (fun _ _ => CF.collapseValue grade value) := by
 unfold actualSourceSlotWrite
 dsimp only
 rw [eval_language language,CF.code_base_value]
 have input : ((language ▸ AS.write factory grade data sourceCfg language value : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) () ())=value := by
  cases sourceCfg with
  | mk lowVar datum inventory pairInventory =>
   change lowVar=C.Var at language
   cases language
   simp only [AS.write,dite_true]
 have env : (fun target name => CF.collapseValue grade
   ((language ▸ AS.write factory grade data sourceCfg language value : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) target name))=
   (fun _ _ => CF.collapseValue grade value) := by
  funext target name
  cases target
  cases name
  rw [input]
 rw [env]

/-- This initialization receipt produces raw slots from the actual old-paid/native source total. Complete inherited source is kept as that total and its original history, not identified with the output slots. -/
theorem source_init_born_raw_slots (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((sourceInitBorn t factory grade data sourceCfg language).activeEnvironment () name)=
 sourceRawSlots (sourceRawFeet (sourceExpandedQuarterReader t
  (originalField (CF.collapseValue grade (sourceInitUpdatedValue t factory grade data sourceCfg language)))) 0) := by
 rw [source_init_active_environment,source_slot_write_read]
 rw [source_init_code_read]
 change sourceInitialSlots t (CF.collapseValue grade (sourceInitUpdatedValue t factory grade data sourceCfg language))=_
 exact source_initial_slots_generated _ _
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
