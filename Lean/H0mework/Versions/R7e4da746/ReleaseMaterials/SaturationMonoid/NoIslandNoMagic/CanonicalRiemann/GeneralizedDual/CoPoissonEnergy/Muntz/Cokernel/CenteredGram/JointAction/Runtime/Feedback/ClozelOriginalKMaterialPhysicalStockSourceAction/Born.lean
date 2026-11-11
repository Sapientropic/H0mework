import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace Complete
export OriginalKWholePaNativeRankSourceUpdate.StockComplete (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Shared
export OriginalKWholePaNativeRankSourceUpdate.StockShared (nextBorn)
end Shared
namespace Environment
export OriginalKWholePaNativeRankSourceUpdate.StockEnvironment (At active)
end Environment
namespace Receiver
export OriginalKWholePaNativeRankSourceUpdate.StockAS (receiver)
end Receiver
namespace NativeValue
export OriginalKWholePaNativeRankSourceUpdate.StockWB (nativeEventValue)
end NativeValue
namespace CF
export OriginalKFullSourceRAction.CF (collapseValue code_base_value)
end CF
local instance paBornGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

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

variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)
variable (N : ℕ)

theorem physical_stock_write_code_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (physicalStockWriteCode N).eval environment = environment () () + sourceMaterialPhysicalStockAction N (environment () ()) := rfl


def physicalStockCfg := AS.stockCfg (physicalStockEmitter factory grade data sourceCfg language N)
def physicalStockReceipt := Complete.receipt (physicalStockCfg factory grade data sourceCfg language N)
 (Receiver.receiver factory grade data sourceCfg language) 0
def physicalStockSelected := Complete.atReceipt (physicalStockCfg factory grade data sourceCfg language N)
 (Receiver.receiver factory grade data sourceCfg language) 0
def physicalStockBorn := Shared.nextBorn (physicalStockSelected factory grade data sourceCfg language N)
 (physicalStockCfg factory grade data sourceCfg language N)
def physicalStockUpdatedValue : PairValue (L.Value (PairValue C.Value) grade) () :=
 WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from (physicalStockReceipt factory grade data sourceCfg language N).2.1.1)

theorem physical_stock_environment : Environment.At (physicalStockBorn factory grade data sourceCfg language N)
 (physicalStockWrite factory grade data sourceCfg language N (physicalStockUpdatedValue factory grade data sourceCfg language N)) := by
 intro current occurrence
 change physicalStockWrite factory grade data sourceCfg language N
  (WB.oldPaid data.1 sourceCfg +
   (show PairValue (L.Value (PairValue C.Value) grade) () from NativeValue.nativeEventValue (physicalStockSelected factory grade data sourceCfg language N).event)) = _
 exact congrArg (fun value => physicalStockWrite factory grade data sourceCfg language N (WB.oldPaid data.1 sourceCfg+value))
  (native_receipt_value _ _)

theorem physical_stock_active_environment : (physicalStockBorn factory grade data sourceCfg language N).activeEnvironment =
 physicalStockWrite factory grade data sourceCfg language N (physicalStockUpdatedValue factory grade data sourceCfg language N) :=
 Environment.active (physical_stock_environment factory grade data sourceCfg language N)

theorem physical_stock_write_field (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (physicalStockWrite factory grade data sourceCfg language N value () name) =
 CF.collapseValue grade value + sourceMaterialPhysicalStockAction N (CF.collapseValue grade value) := by
 unfold physicalStockWrite
 dsimp only
 rw [eval_language language]
 rw [CF.code_base_value,physical_stock_write_code_read]
 have input : ((language ▸ AS.write factory grade data sourceCfg language value : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) () ()) = value := by
  cases sourceCfg with
  | mk lowVar datum inventory pairInventory =>
   change lowVar=C.Var at language
   cases language
   simp only [AS.write,dite_true]
 rw [input]

theorem physical_stock_generated_source_delta (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((physicalStockBorn factory grade data sourceCfg language N).activeEnvironment () name) -
 CF.collapseValue grade (physicalStockUpdatedValue factory grade data sourceCfg language N) = sourceMaterialPhysicalStockAction N (CF.collapseValue grade (physicalStockUpdatedValue factory grade data sourceCfg language N)) := by
 rw [physical_stock_active_environment,physical_stock_write_field]
 exact add_sub_cancel_left _ _


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
