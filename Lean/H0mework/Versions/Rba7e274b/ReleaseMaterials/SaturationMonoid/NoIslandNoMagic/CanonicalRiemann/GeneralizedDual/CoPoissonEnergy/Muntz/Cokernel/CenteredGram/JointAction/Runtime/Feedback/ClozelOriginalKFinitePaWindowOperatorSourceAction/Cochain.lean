import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Inverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open SourceOperationScalarRelations

def sourceStockWord (radius : ℝ) (source : Branches) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.var ()) ((completeWindowWord radius).subst (fun _ _ => .const source))

theorem source_stock_word_value (radius : ℝ) (source : Branches) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceStockWord radius source).eval environment = environment () () +
  (completeWindowWord radius).eval (windowEnvironment source) := by
 unfold sourceStockWord
 rw [Expr.eval,Expr.eval_subst]
 rfl

def sourceStockIncrement (radius : ℝ) (source : Branches) : Branches :=
 (completeWindowWord radius).eval (windowEnvironment source)

def boundCochainWord (radius : ℝ) (source old : Branches) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 (SourceOperationExecution.Cochain.expression (Finsupp.single (sourceStockWord radius source) (1:ℤ))).subst
  (fun _ coordinate => match coordinate.2 with
   | .old => .const old
   | .increment => .const (sourceStockIncrement radius source))

theorem bound_cochain_source_zero (radius : ℝ) (source old : Branches)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (boundCochainWord radius source old).eval environment = 0 := by
 unfold boundCochainWord
 rw [Expr.eval_subst]
 have same : (fun target (coordinate : ChangedVar C.Var target) =>
   (match coordinate.2 with
    | .old => Expr.const old
    | .increment => Expr.const (sourceStockIncrement radius source) : Expr (PairValue (PairValue C.Value)) C.Var ()).eval environment) =
   mixedEnvironment (windowEnvironment old) (windowEnvironment (sourceStockIncrement radius source)) := by
  funext target coordinate
  cases target
  rcases coordinate with ⟨name,part⟩
  cases part <;> rfl
 rw [same]
 exact SourceOperationExecution.Cochain.source_zero (windowEnvironment old)
  (windowEnvironment (sourceStockIncrement radius source)) _

def boundCochainTrace (radius : ℝ) (source old : Branches) :
 Trace (windowEnvironment old) (boundCochainWord radius source old) (.const 0) := by
 have generated := execution (windowEnvironment old) (boundCochainWord radius source old)
 rw [bound_cochain_source_zero] at generated
 exact generated

def completeSourceInventory (radius : ℝ) (source old : Branches) :=
 SourceHistoryCommon.seed (completeWindowInventory radius source)
  (SourceOperationPaidRelations.exposure (boundCochainTrace radius source old))

theorem complete_cutoff_relation_inventory (radius : ℝ) (source : Branches) (increment : Env (PairValue (PairValue C.Value)) C.Var) :
 type_of% ((finiteWindowTrace radius source).relation_inventory (R:=ℤ) increment) :=
 (finiteWindowTrace radius source).relation_inventory (R:=ℤ) increment

theorem complete_cutoff_cochain_relation (radius : ℝ) (source : Branches) (increment : Env (PairValue (PairValue C.Value)) C.Var) :
 type_of% ((finiteWindowTrace radius source).relation_cochain (R:=ℤ) increment) :=
 (finiteWindowTrace radius source).relation_cochain (R:=ℤ) increment

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
