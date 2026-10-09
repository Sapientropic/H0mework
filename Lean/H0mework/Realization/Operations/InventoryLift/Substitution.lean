import H0mework.Realization.Operations.InventoryLift
set_option autoImplicit false
noncomputable section
universe r u v w w'
namespace SaturationMonoid.SourceOperationScalarInventoryLift
open SourceOperationEffects SourceOperationScalarRelations
namespace SubstitutionLift
variable {S : Type u} {V : S → Type v} {X : S → Type w} {Y : S → Type w'}
variable [∀ t,AddCommGroup (V t)]
variable (binding : ∀ t,X t → Expr V Y t)
theorem expression {s : S} (term : Expr V X s) :
 liftExpr (term.subst binding)=
 (liftExpr term).subst (fun t name=>liftExpr (binding t name)) :=
 Expr.rec
  (motive:=fun _ term=>liftExpr (term.subst binding)=
   (liftExpr term).subst (fun t name=>liftExpr (binding t name)))
  (fun {_} _=>rfl)
  (fun {_} _=>rfl)
  (fun {_} _ _ left right=>congrArg₂ Expr.add left right)
  (fun {_ _} f _ argument=>congrArg (Expr.linear (pairLinear f)) argument)
  (fun {_ _ _} f _ _ left right=>congrArg₂ (Expr.bilinear (pairBilinear f)) left right) term
variable {R : Type r} [CommRing R]
theorem word {s : S} :
 (liftMap (R:=R) (s:=s)).comp (substitution (R:=R) binding)=
 (substitution (R:=R) (fun t name=>liftExpr (binding t name))).comp liftMap :=by
 apply Finsupp.lhom_ext
 intro term coefficient
 simp only [LinearMap.comp_apply,liftMap,substitution,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
 exact congrArg (fun term=>Finsupp.single term coefficient) (expression binding term)
end SubstitutionLift
end SaturationMonoid.SourceOperationScalarInventoryLift
end
