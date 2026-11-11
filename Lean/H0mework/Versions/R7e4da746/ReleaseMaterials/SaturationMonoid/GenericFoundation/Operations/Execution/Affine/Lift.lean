import H0mework.Realization.Operations.Execution.Relations
import H0mework.Realization.Operations.InventoryLift

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSigmaAffineAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceOperationScalarInventoryLift
variable {Sorts : Type} {Value Var : Sorts→Type}
 [∀ target,AddCommGroup (Value target)] {sort : Sorts}

theorem lift_affine_effect (raw : Expr Value Var sort) (value : Value sort)
 (old increment : Env (PairValue Value) Var) :
 (liftExpr (.add raw (.linear (-AddMonoidHom.id _) (.const value)))).effect old increment=
 (liftExpr raw).effect old increment := by
 simp only [liftExpr,Expr.effect,map_zero,add_zero]

theorem literal_boundary_effect (before : Expr Value Var sort) (value : Value sort)
 (old increment : Env Value Var) :
 effectEvaluator (R:=ℤ) old increment
  (Finsupp.single before (1:ℤ)-Finsupp.single (.const value) 1)=before.effect old increment := by
 simp only [map_sub,Finsupp.linearCombination_single,one_smul,Expr.effect,sub_zero]

theorem lift_literal_boundary_effect (before : Expr Value Var sort) (value : Value sort)
 (old increment : Env (PairValue Value) Var) :
 effectEvaluator (R:=ℤ) old increment
  (liftMap (R:=ℤ) (Finsupp.single before (1:ℤ)-Finsupp.single (.const value) 1))=
 (liftExpr before).effect old increment := by
 simp only [map_sub,liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
  Finsupp.linearCombination_single,one_smul,liftExpr,Expr.effect,sub_zero]

end SourceSigmaAffineAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
