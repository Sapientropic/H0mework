import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Transition
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance traceGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

private theorem eval_language {Y Z : Unit → Type} (same : Y=Z)
 {Value : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (code : Expr Value Z ()) (environment : Env Value Y) :
 (same.symm ▸ code : Expr Value Y ()).eval environment = code.eval (same ▸ environment : Env Value Z) := by
 cases same
 rfl

private theorem receipt_native_value {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 NativeValue.nativeEventValue (Complete.atReceipt cfg initial 0).event = (Complete.receipt cfg initial 0).2.1.1 := by
 have receipt := (Complete.receipt cfg initial 0).2.2.2
 change RootGeneratedDebtActivationJointSource.mathAction (Complete.atReceipt cfg initial 0).event = Sum.inl (Complete.receipt cfg initial 0).2.1 at receipt
 unfold NativeValue.nativeEventValue
 rw [receipt]

/-- The actual inventory Trace is consumed at its source environment, before its physical stock or tail reaches a cotest. -/
theorem physical_received_inventory_trace_action (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (endpoint : PairValue (L.Value (PairValue C.Value) grade) ())
    (trace : Trace (physicalSourceRaw factory grade data sourceCfg language code
      (physicalStockSelected factory grade data sourceCfg language N)).environment
      (physicalSourceRaw factory grade data sourceCfg language code
        (physicalStockSelected factory grade data sourceCfg language N)).expression (.const endpoint)) :
    CF.collapseValue grade endpoint = code.eval (fun _ _ => actualMaterialStockSourceTotal factory grade data sourceCfg language N) := by
  have generated := congrArg (CF.collapseValue grade) trace.sound
  change CF.collapseValue grade ((physicalSourceRaw factory grade data sourceCfg language code
    (physicalStockSelected factory grade data sourceCfg language N)).expression.eval
    (physicalSourceRaw factory grade data sourceCfg language code
      (physicalStockSelected factory grade data sourceCfg language N)).environment) = CF.collapseValue grade endpoint at generated
  unfold physicalSourceRaw OriginalKFinitePaWindowOperatorSourceAction.sourceLiteralRaw at generated
  dsimp only at generated
  rw [eval_language language,CF.code_base_value] at generated
  have sourceValue : ((language ▸ AS.write factory grade data sourceCfg language
      (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg (physicalStockSelected factory grade data sourceCfg language N)
        (S.actualOccurrence (physicalStockSelected factory grade data sourceCfg language N))) :
      Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) () ()) = physicalStockUpdatedValue factory grade data sourceCfg language N := by
    have actual := receipt_native_value (physicalStockCfg factory grade data sourceCfg language N)
      (Receiver.receiver factory grade data sourceCfg language)
    have native : WB.nativeAt sourceCfg (physicalStockSelected factory grade data sourceCfg language N)
        (S.actualOccurrence (physicalStockSelected factory grade data sourceCfg language N)) =
      (show PairValue (L.Value (PairValue C.Value) grade) () from
        (physicalStockReceipt factory grade data sourceCfg language N).2.1.1) := by
      exact actual
    have updated := congrArg (fun value : PairValue (L.Value (PairValue C.Value) grade) () => WB.oldPaid data.1 sourceCfg + value) native
    cases sourceCfg with
    | mk lowVar datum inventory pairInventory =>
      change lowVar=C.Var at language
      cases language
      simp only [AS.write,dite_true]
      exact updated
  have environment : (fun target name => CF.collapseValue grade
      ((language ▸ AS.write factory grade data sourceCfg language
        (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg (physicalStockSelected factory grade data sourceCfg language N)
          (S.actualOccurrence (physicalStockSelected factory grade data sourceCfg language N))) :
        Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) target name)) =
      (fun _ _ => actualMaterialStockSourceTotal factory grade data sourceCfg language N) := by
    funext target name
    cases target
    cases name
    rw [sourceValue]
    rfl
  rw [environment] at generated
  exact generated.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
