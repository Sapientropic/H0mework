import H0mework.Realization.MappingCone.AdjugateInclusion

/-!
# Canonical determinant-adjugate total fibre

For cochain endomorphisms `T`, `D`, and `Q` satisfying `Q ≫ T = D`, the
pair `(Q, id)` lands in the kernel of the actual row `[T, -D]`.  The mapping-
cocone universal property therefore generates one chain map

`C ⟶ Fib([T,-D])`.

Its second source coordinate is literally `id_C`.  Thus arbitrary endpoint
elements and their existing differentials enter the same generated total
fibre without an endpoint-cycle premise.  Unlike transport of the ordinary
`inr`, this construction loses its type when either the adjugate or
determinant row is removed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace CochainMappingCoconeDeterminantAdjugateTotalFiber

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainMappingCoconeDeterminantAdjugateInclusion

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasBinaryBiproducts C]
variable {K : CochainComplex C ℤ}
variable {actionOperator determinantMultiplication adjugate : K ⟶ K}
variable (actual : ActionDeterminantAdjugateAt
  actionOperator determinantMultiplication adjugate)

include actual

/-- The actual two-column Koszul row `[T,-D]`. -/
noncomputable def totalRow
    (actionOperator determinantMultiplication : K ⟶ K) : K ⊞ K ⟶ K :=
  biprod.desc actionOperator (-determinantMultiplication)

/-- The canonical syzygy column `(Q,id)`. -/
noncomputable def totalKernelPair (adjugate : K ⟶ K) : K ⟶ K ⊞ K :=
  biprod.lift adjugate (𝟙 K)

theorem totalKernelPair_row_zero :
    totalKernelPair adjugate ≫
        totalRow actionOperator determinantMultiplication = 0 := by
  rw [totalKernelPair, totalRow, biprod.lift_desc]
  rw [ActionDeterminantAdjugateAt.factorization actual]
  simp

noncomputable abbrev TotalFiber
    (actionOperator determinantMultiplication : K ⟶ K) :=
  CochainComplex.mappingCocone
    (totalRow actionOperator determinantMultiplication)

/-- Framework-generated total-fibre inclusion of the entire source complex.
The endpoint is not chosen here. -/
noncomputable def totalInclusion :
    K ⟶ TotalFiber actionOperator determinantMultiplication :=
  CochainComplex.mappingCocone.lift
    (totalRow actionOperator determinantMultiplication)
    (totalKernelPair adjugate) 0 (by
      rw [totalKernelPair_row_zero actual]
      simp)

@[reassoc (attr := simp)] theorem totalInclusion_fst :
    totalInclusion actual ≫
        CochainComplex.mappingCocone.fst
          (totalRow actionOperator determinantMultiplication) =
      totalKernelPair adjugate :=
  CochainComplex.mappingCocone.lift_fst
    (totalRow actionOperator determinantMultiplication)
    (totalKernelPair adjugate) 0 (by
      rw [totalKernelPair_row_zero actual]
      simp)

/-- First coordinate reads the canonical adjugate action. -/
@[reassoc] theorem totalInclusion_adjugate_readback :
    totalInclusion actual ≫
        CochainComplex.mappingCocone.fst
          (totalRow actionOperator determinantMultiplication) ≫
        (biprod.fst : K ⊞ K ⟶ K) =
      adjugate := by
  rw [← Category.assoc, totalInclusion_fst]
  simp [totalKernelPair]

/-- Second coordinate is the literal original whole complex. -/
@[reassoc] theorem totalInclusion_endpoint_readback :
    totalInclusion actual ≫
        CochainComplex.mappingCocone.fst
          (totalRow actionOperator determinantMultiplication) ≫
        (biprod.snd : K ⊞ K ⟶ K) =
      𝟙 K := by
  rw [← Category.assoc, totalInclusion_fst]
  simp [totalKernelPair]

/-- The same identity degreewise: endpoint values and their actual
differentials are transported by one chain map. -/
@[reassoc] theorem totalInclusion_endpoint_readback_f (degree : ℤ) :
    (totalInclusion actual).f degree ≫
        (CochainComplex.mappingCocone.fst
          (totalRow actionOperator determinantMultiplication)).f degree ≫
        (biprod.snd : K ⊞ K ⟶ K).f degree =
      𝟙 (K.X degree) := by
  have generated := congrArg (fun arrow ↦ arrow.f degree)
    (totalInclusion_endpoint_readback actual)
  simp only [HomologicalComplex.comp_f] at generated
  change _ = HomologicalComplex.Hom.f (𝟙 K) degree
  exact generated

end
end CochainMappingCoconeDeterminantAdjugateTotalFiber
end SaturationMonoid
