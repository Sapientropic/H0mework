import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
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
local instance residualBornGroups (grade : Nat) (target : Unit) :
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
variable (radius : ℝ) (source residual : F.Branches)

def residualStockCfg := AS.stockCfg (residualEmitterStock factory grade data sourceCfg language radius source residual)
def residualStockReceipt := Complete.receipt (residualStockCfg factory grade data sourceCfg language radius source residual)
 (Receiver.receiver factory grade data sourceCfg language) 0
def residualStockSelected := Complete.atReceipt (residualStockCfg factory grade data sourceCfg language radius source residual)
 (Receiver.receiver factory grade data sourceCfg language) 0
def residualStockBorn := Shared.nextBorn (residualStockSelected factory grade data sourceCfg language radius source residual)
 (residualStockCfg factory grade data sourceCfg language radius source residual)
def residualStockUpdatedValue : PairValue (L.Value (PairValue C.Value) grade) () :=
 WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from (residualStockReceipt factory grade data sourceCfg language radius source residual).2.1.1)

theorem residual_stock_environment : Environment.At (residualStockBorn factory grade data sourceCfg language radius source residual)
 (residualStockWrite factory grade data sourceCfg language radius source residual (residualStockUpdatedValue factory grade data sourceCfg language radius source residual)) := by
 intro current occurrence
 change residualStockWrite factory grade data sourceCfg language radius source residual
  (WB.oldPaid data.1 sourceCfg +
   (show PairValue (L.Value (PairValue C.Value) grade) () from NativeValue.nativeEventValue (residualStockSelected factory grade data sourceCfg language radius source residual).event)) = _
 exact congrArg (fun value => residualStockWrite factory grade data sourceCfg language radius source residual (WB.oldPaid data.1 sourceCfg+value))
  (native_receipt_value _ _)

theorem residual_stock_active_environment : (residualStockBorn factory grade data sourceCfg language radius source residual).activeEnvironment =
 residualStockWrite factory grade data sourceCfg language radius source residual (residualStockUpdatedValue factory grade data sourceCfg language radius source residual) :=
 Environment.active (residual_stock_environment factory grade data sourceCfg language radius source residual)

theorem residual_stock_write_field (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (residualStockWrite factory grade data sourceCfg language radius source residual value () name) =
 CF.collapseValue grade value + (residualWindowCode radius source residual).eval (F.windowEnvironment source) := by
 unfold residualStockWrite
 dsimp only
 rw [eval_language language]
 rw [CF.code_base_value,residual_stock_source_value,residual_window_source_value]
 congr 1
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  simp only [AS.write,dite_true]

theorem residual_stock_generated_source_delta (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((residualStockBorn factory grade data sourceCfg language radius source residual).activeEnvironment () name) -
 CF.collapseValue grade (residualStockUpdatedValue factory grade data sourceCfg language radius source residual) = (residualWindowCode radius source residual).eval (F.windowEnvironment source) := by
 rw [residual_stock_active_environment,residual_stock_write_field]
 exact add_sub_cancel_left _ _

theorem residual_stock_window_effect (name : sourceCfg.LowVar ()) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField
  (CF.collapseValue grade ((residualStockBorn factory grade data sourceCfg language radius source residual).activeEnvironment () name) -
   CF.collapseValue grade (residualStockUpdatedValue factory grade data sourceCfg language radius source residual))) -
 windowObservation radius source = -windowObservation radius residual := by
 rw [residual_stock_generated_source_delta]
 exact residual_window_from_received_trace radius source residual _ (residualWindowTrace radius source residual)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
