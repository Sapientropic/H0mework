import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
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
variable (source : D.SourceBranches)

def paStockCfg := AS.stockCfg (sourcePaEmitterStock factory grade data sourceCfg language source)
def paStockReceipt := Complete.receipt (paStockCfg factory grade data sourceCfg language source)
 (Receiver.receiver factory grade data sourceCfg language) 0
def paStockSelected := Complete.atReceipt (paStockCfg factory grade data sourceCfg language source)
 (Receiver.receiver factory grade data sourceCfg language) 0
def paStockBorn := Shared.nextBorn (paStockSelected factory grade data sourceCfg language source)
 (paStockCfg factory grade data sourceCfg language source)
def paStockUpdatedValue : PairValue (L.Value (PairValue C.Value) grade) () :=
 WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from (paStockReceipt factory grade data sourceCfg language source).2.1.1)

theorem pa_stock_environment : Environment.At (paStockBorn factory grade data sourceCfg language source)
 (sourcePaStockWrite factory grade data sourceCfg language source (paStockUpdatedValue factory grade data sourceCfg language source)) := by
 intro current occurrence
 change sourcePaStockWrite factory grade data sourceCfg language source
  (WB.oldPaid data.1 sourceCfg +
   (show PairValue (L.Value (PairValue C.Value) grade) () from NativeValue.nativeEventValue (paStockSelected factory grade data sourceCfg language source).event)) = _
 exact congrArg (fun value => sourcePaStockWrite factory grade data sourceCfg language source (WB.oldPaid data.1 sourceCfg+value))
  (native_receipt_value _ _)

theorem pa_stock_active_environment : (paStockBorn factory grade data sourceCfg language source).activeEnvironment =
 sourcePaStockWrite factory grade data sourceCfg language source (paStockUpdatedValue factory grade data sourceCfg language source) :=
 Environment.active (pa_stock_environment factory grade data sourceCfg language source)

theorem pa_stock_write_field (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (sourcePaStockWrite factory grade data sourceCfg language source value () name) =
 CF.collapseValue grade value + sourcePaSourceAction source := by
 unfold sourcePaStockWrite
 dsimp only
 rw [eval_language language]
 rw [CF.code_base_value,source_pa_stock_code]
 congr 1
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  simp only [AS.write,dite_true]

theorem pa_stock_generated_source_delta (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((paStockBorn factory grade data sourceCfg language source).activeEnvironment () name) -
 CF.collapseValue grade (paStockUpdatedValue factory grade data sourceCfg language source) = sourcePaSourceAction source := by
 rw [pa_stock_active_environment,pa_stock_write_field]
 exact add_sub_cancel_left _ _

theorem pa_stock_source_window (name : sourceCfg.LowVar ()) (radius : ℝ) :
 burnolSourceOnlyCoPoissonWindow radius
  (OriginalKFullSourceRAction.originalField
   (CF.collapseValue grade ((paStockBorn factory grade data sourceCfg language source).activeEnvironment () name) -
    CF.collapseValue grade (paStockUpdatedValue factory grade data sourceCfg language source))) =
 burnolRadiusRestriction radius (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField source) : BurnolL2) := by
 rw [pa_stock_generated_source_delta]
 change burnolSourceOnlyCoPoissonWindow radius (OriginalKFullSourceRAction.originalField (Native.sourceFields (sourcePaMobius source))) = _
 rw [Native.source_fields_first]
 exact source_pa_window_generated radius source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
