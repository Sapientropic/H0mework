import H0mework.Realization.MappingCone.Degreewise
import H0mework.Realization.MappingCone.Functoriality

/-!
# Determinant-adjugate descent into an action mapping cocone

For cochain endomorphisms `T`, `D`, and `Q` with `Q ≫ T = D`, mapping-cocone
functoriality transports the tautological inclusion of `Fib(D)` into the
already generated action fibre `Fib(T)`.  Its shifted-target readback is
literally the identity on the original complex.

This is the family-level closure needed when an endpoint is not itself a
cycle: the construction acts on the whole complex, so every endpoint and its
actual differential travel together.  No selected endpoint, kernel element,
zero law, fixedness, or inverse enters the interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace CochainMappingCoconeDeterminantAdjugateInclusion

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainMappingCoconeDegreewiseKernel
open CochainMappingCoconeFunctoriality

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasBinaryBiproducts C]
variable {K : CochainComplex C ℤ}

/-- The actual determinant-adjugate square on one whole cochain complex. -/
structure ActionDeterminantAdjugateAt
    (actionOperator determinantMultiplication adjugate : K ⟶ K) : Prop where
  factorization : adjugate ≫ actionOperator = determinantMultiplication

namespace ActionDeterminantAdjugateAt

variable {actionOperator determinantMultiplication adjugate : K ⟶ K}
variable (actual : ActionDeterminantAdjugateAt
  actionOperator determinantMultiplication adjugate)

include actual

omit [Limits.HasBinaryBiproducts C] in
theorem arrowSquare :
    adjugate ≫ actionOperator =
      determinantMultiplication ≫ 𝟙 K := by
  simpa using ActionDeterminantAdjugateAt.factorization actual

/-- The canonical arrow-square map from the determinant fibre to the action
fibre.  The right leg is the identity, so it preserves the whole source
coordinate rather than choosing an element. -/
noncomputable def determinantToActionCofiberMap :
    CochainComplex.mappingCocone determinantMultiplication ⟶
      CochainComplex.mappingCocone actionOperator :=
  mappingCoconeMap determinantMultiplication actionOperator
    adjugate (𝟙 K) (arrowSquare actual)

noncomputable def generatedInclusionCochain :
    Cochain K (CochainComplex.mappingCocone actionOperator) 1 :=
  (CochainComplex.mappingCocone.inr determinantMultiplication).1.comp
    (Cochain.ofHom (determinantToActionCofiberMap actual)) (add_zero 1)

omit actual in
private theorem mappingCoconeMap_inr_between
    {K' L' : CochainComplex C ℤ}
    (arrow : K ⟶ K') (targetArrow : K ⟶ L')
    (left : K ⟶ K) (right : K' ⟶ L')
    (square : left ≫ targetArrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inr arrow).1.comp
        (Cochain.ofHom
          (mappingCoconeMap arrow targetArrow left right square))
          (add_zero 1) =
      (Cochain.ofHom right).comp
        (CochainComplex.mappingCocone.inr targetArrow).1
          (zero_add 1) := by
  ext sourceDegree targetDegree degreeEq : 1
  rw [Cochain.comp_v _ _ (add_zero 1)
      sourceDegree targetDegree targetDegree degreeEq
        (add_zero targetDegree),
    Cochain.comp_v _ _ (zero_add 1)
      sourceDegree sourceDegree targetDegree
        (add_zero sourceDegree) degreeEq]
  simp only [Cochain.ofHom_v]
  apply degree_hom_ext_at targetArrow targetDegree sourceDegree (by omega)
  · have generated := congrArg (fun map ↦ map.f targetDegree)
      (mappingCoconeMap_fst arrow targetArrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [Category.assoc, generated]
    simp
  · have generated := Cochain.congr_v
      (mappingCoconeMap_snd arrow targetArrow left right square)
      targetDegree sourceDegree (by omega)
    have generatedComponent :
        (mappingCoconeMap arrow targetArrow left right square).f targetDegree ≫
            (CochainComplex.mappingCocone.snd targetArrow).v
              targetDegree sourceDegree (by omega) =
          (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) ≫
            right.f sourceDegree := by
      simpa [Cochain.comp_v] using generated
    rw [Category.assoc, generatedComponent]
    simp [Category.assoc]

/-- The determinant-supported inclusion is the same tautological action-
fibre inclusion, now generated through the actual adjugate square. -/
theorem generatedInclusionCochain_eq_tautological :
    generatedInclusionCochain actual =
      (CochainComplex.mappingCocone.inr actionOperator).1 := by
  unfold generatedInclusionCochain determinantToActionCofiberMap
  rw [mappingCoconeMap_inr_between determinantMultiplication
    actionOperator adjugate (𝟙 K) (arrowSquare actual)]
  simp

/-- Family-level determinant-supported inclusion. -/
noncomputable def generatedInclusion :
    Cocycle K (CochainComplex.mappingCocone actionOperator) 1 := by
  refine ⟨generatedInclusionCochain actual, ?_⟩
  rw [generatedInclusionCochain_eq_tautological actual]
  exact (CochainComplex.mappingCocone.inr actionOperator).2

/-- The generated inclusion reads back the exact whole source complex. -/
theorem generatedInclusion_readback :
    (generatedInclusion actual).1.comp
        (CochainComplex.mappingCocone.snd actionOperator)
          (add_neg_cancel (1 : ℤ)) =
      Cochain.ofHom (𝟙 K) := by
  rw [show (generatedInclusion actual).1 =
      (CochainComplex.mappingCocone.inr actionOperator).1 by
    exact generatedInclusionCochain_eq_tautological actual]
  ext sourceDegree : 1
  rw [Cochain.comp_v _ _ (add_neg_cancel (1 : ℤ))
    sourceDegree (sourceDegree + 1) sourceDegree rfl (by omega)]
  convert CochainComplex.mappingCocone.inr_v_snd_v
    actionOperator sourceDegree (sourceDegree + 1) rfl using 1
  all_goals simp [Cochain.ofHom_v]

@[reassoc] theorem generatedInclusion_readback_v
    (degree : ℤ) :
    (generatedInclusion actual).1.v degree (degree + 1) rfl ≫
        (CochainComplex.mappingCocone.snd actionOperator).v
          (degree + 1) degree (by omega) =
      𝟙 (K.X degree) := by
  have generated := Cochain.congr_v (generatedInclusion_readback actual)
    degree degree (add_zero degree)
  simpa [Cochain.comp_v] using generated

end ActionDeterminantAdjugateAt

end
end CochainMappingCoconeDeterminantAdjugateInclusion
end SaturationMonoid
