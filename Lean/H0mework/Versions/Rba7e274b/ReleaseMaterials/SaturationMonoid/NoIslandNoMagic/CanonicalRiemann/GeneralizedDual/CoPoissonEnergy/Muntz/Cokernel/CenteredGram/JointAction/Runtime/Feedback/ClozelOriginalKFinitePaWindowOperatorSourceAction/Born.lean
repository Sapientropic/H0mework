import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
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
local instance finiteBornGroups (grade : Nat) (target : Unit) :
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
variable (radius : ℝ) (source : Branches)

def finiteStockCfg := AS.stockCfg (finiteEmitterStock factory grade data sourceCfg language radius source)
def finiteStockReceipt := Complete.receipt (finiteStockCfg factory grade data sourceCfg language radius source)
 (Receiver.receiver factory grade data sourceCfg language) 0
def finiteStockSelected := Complete.atReceipt (finiteStockCfg factory grade data sourceCfg language radius source)
 (Receiver.receiver factory grade data sourceCfg language) 0
def finiteStockBorn := Shared.nextBorn (finiteStockSelected factory grade data sourceCfg language radius source)
 (finiteStockCfg factory grade data sourceCfg language radius source)
def finiteStockUpdatedValue : PairValue (L.Value (PairValue C.Value) grade) () :=
 WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from (finiteStockReceipt factory grade data sourceCfg language radius source).2.1.1)

theorem finite_stock_environment : Environment.At (finiteStockBorn factory grade data sourceCfg language radius source)
 (finiteStockWrite factory grade data sourceCfg language radius source (finiteStockUpdatedValue factory grade data sourceCfg language radius source)) := by
 intro current occurrence
 change finiteStockWrite factory grade data sourceCfg language radius source
  (WB.oldPaid data.1 sourceCfg +
   (show PairValue (L.Value (PairValue C.Value) grade) () from NativeValue.nativeEventValue (finiteStockSelected factory grade data sourceCfg language radius source).event)) = _
 exact congrArg (fun value => finiteStockWrite factory grade data sourceCfg language radius source (WB.oldPaid data.1 sourceCfg+value))
  (native_receipt_value _ _)

theorem finite_stock_active_environment : (finiteStockBorn factory grade data sourceCfg language radius source).activeEnvironment =
 finiteStockWrite factory grade data sourceCfg language radius source (finiteStockUpdatedValue factory grade data sourceCfg language radius source) :=
 Environment.active (finite_stock_environment factory grade data sourceCfg language radius source)

theorem finite_stock_write_field (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (finiteStockWrite factory grade data sourceCfg language radius source value () name) =
 CF.collapseValue grade value + (completeWindowWord radius).eval (windowEnvironment source) := by
 unfold finiteStockWrite
 dsimp only
 rw [eval_language language]
 rw [CF.code_base_value,source_stock_word_value]
 congr 1
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  simp only [AS.write,dite_true]

theorem finite_stock_generated_source_delta (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((finiteStockBorn factory grade data sourceCfg language radius source).activeEnvironment () name) -
 CF.collapseValue grade (finiteStockUpdatedValue factory grade data sourceCfg language radius source) = (completeWindowWord radius).eval (windowEnvironment source) := by
 rw [finite_stock_active_environment,finite_stock_write_field]
 exact add_sub_cancel_left _ _

theorem finite_stock_source_window (name : sourceCfg.LowVar ()) :
 burnolRadiusRestriction radius (OriginalKFullSourceRAction.originalField
  (CF.collapseValue grade ((finiteStockBorn factory grade data sourceCfg language radius source).activeEnvironment () name) -
   CF.collapseValue grade (finiteStockUpdatedValue factory grade data sourceCfg language radius source))) =
 burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField source) := by
 rw [finite_stock_generated_source_delta]
 exact window_from_received_trace radius source _ (finiteWindowTrace radius source)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
