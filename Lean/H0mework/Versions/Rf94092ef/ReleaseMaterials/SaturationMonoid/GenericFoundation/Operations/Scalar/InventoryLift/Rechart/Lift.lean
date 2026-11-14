import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Scalar.InventoryLift.Rechart

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.SourceOperationScalarInventoryLift.Rechart

open SourceOperationEffects SourceOperationScalarRelations

open private linear bilinear word_single from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Scalar.InventoryLift.Rechart

universe u
variable {S : Type u} {V W X : S → Type u}
variable [∀ s, AddCommGroup (V s)] [∀ s, AddCommGroup (W s)]
variable (chart : ∀ s, V s ≃+ W s)

abbrev pairChart (s : S) : PairValue V s ≃+ PairValue W s :=
  (chart s).prodCongr (chart s)

private theorem linear_pair {s t : S} (operation : V s →+ V t) :
    linear (pairChart chart) (pairLinear operation) = pairLinear (linear chart operation) := by
  apply AddMonoidHom.ext
  intro value
  rfl

private theorem bilinear_pair {s t r : S} (operation : V s →+ V t →+ V r) :
    bilinear (pairChart chart) (pairBilinear operation) = pairBilinear (bilinear chart operation) := by
  apply AddMonoidHom.ext
  rintro ⟨left, incrementLeft⟩
  apply AddMonoidHom.ext
  rintro ⟨right, incrementRight⟩
  let a := (chart s).symm left
  let da := (chart s).symm incrementLeft
  let b := (chart t).symm right
  let db := (chart t).symm incrementRight
  let e := chart r
  change (e (operation a b), e (operation a db+operation da b+operation da db)) =
    (e (operation a b), e (operation a db)+e (operation da b)+e (operation da db))
  simp only [map_add]

/-- The actual lift retains the left, right and joint bilinear effects under the same chart. -/
theorem expr_lift {s : S} (term : Expr V X s) :
    expr (pairChart chart) (liftExpr term) = liftExpr (expr chart term) := by
  induction term with
  | var _ => rfl
  | @const s value =>
    exact congrArg (fun input : PairValue W s => Expr.const (Var := X) input)
      (Prod.ext rfl (map_zero (chart s)))
  | add left right hl hr => simp only [liftExpr, expr, hl, hr]
  | linear operation term h => simp only [liftExpr, expr, linear_pair, h]
  | bilinear operation left right hl hr =>
    simp only [liftExpr, expr, bilinear_pair, hl, hr]

/-- Rechart the actual formal word before or after adjoining its old/effect inventory. -/
theorem word_lift {s : S} (relation : Formal ℤ V X s) :
    word (pairChart chart) s (liftMap (R := ℤ) relation) =
      liftMap (R := ℤ) (word chart s relation) := by
  have square : ((word (X := X) (pairChart chart) s).toLinearMap).comp (liftMap (R := ℤ)) =
      (liftMap (R := ℤ)).comp (word (X := X) chart s).toLinearMap := by
    apply Finsupp.lhom_ext
    intro term count
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftMap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, word_single, expr_lift]
  exact LinearMap.congr_fun square relation

end SaturationMonoid.SourceOperationScalarInventoryLift.Rechart
