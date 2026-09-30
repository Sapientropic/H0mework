import H0mework.Realization.MappingCone.AdjugateTotalFiber

/-!
# Shear naturality of determinant-adjugate total fibres

Suppose a successor restriction preserves the action operator while the
determinant and adjugate acquire one common relative factor `ρ`.  A diagonal
map between the two Koszul rows would scale the endpoint.  The canonical
upper-triangular shear

`(q,e) ↦ (R q + R Q (1-ρ)e, R e)`

instead preserves the raw endpoint, intertwines `[T,-D]`, and sends the high
kernel pair `(Q,id)` to the low kernel pair.  Mapping-cocone functoriality then
generates the total-fibre successor; no inverse of `ρ` is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace CochainMappingCoconeDeterminantAdjugateTotalFiberShearNaturality

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CochainMappingCoconeDegreewiseKernel
open CochainMappingCoconeFunctoriality
open CochainMappingCoconeDeterminantAdjugateInclusion
open CochainMappingCoconeDeterminantAdjugateTotalFiber

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasBinaryBiproducts C]
variable {Kₕ Kₗ : CochainComplex C ℤ}
variable {Tₕ Dₕ Qₕ : Kₕ ⟶ Kₕ}
variable {Tₗ Dₗ Qₗ : Kₗ ⟶ Kₗ}

/-- Actual successor data.  `ρ` is the relative determinant action on the
low stage; it is not assumed invertible. -/
structure TotalFiberShearSuccessorAt
    (high : ActionDeterminantAdjugateAt Tₕ Dₕ Qₕ)
    (low : ActionDeterminantAdjugateAt Tₗ Dₗ Qₗ)
    (restriction : Kₕ ⟶ Kₗ) (relative : Kₗ ⟶ Kₗ) : Prop where
  operatorSquare : Tₕ ≫ restriction = restriction ≫ Tₗ
  determinantSquare : Dₕ ≫ restriction =
    restriction ≫ Dₗ ≫ relative
  adjugateSquare : Qₕ ≫ restriction =
    restriction ≫ Qₗ ≫ relative
  relativeOperatorCommutes : relative ≫ Tₗ = Tₗ ≫ relative

namespace TotalFiberShearSuccessorAt

variable {high : ActionDeterminantAdjugateAt Tₕ Dₕ Qₕ}
variable {low : ActionDeterminantAdjugateAt Tₗ Dₗ Qₗ}
variable {restriction : Kₕ ⟶ Kₗ} {relative : Kₗ ⟶ Kₗ}
variable (actual : TotalFiberShearSuccessorAt high low restriction relative)

include actual

noncomputable def correction
    (_actual : TotalFiberShearSuccessorAt high low restriction relative) :
    Kₕ ⟶ Kₗ :=
  restriction ≫ Qₗ ≫ (𝟙 Kₗ - relative)

noncomputable def firstCoordinate
    (actual : TotalFiberShearSuccessorAt high low restriction relative) :
    Kₕ ⊞ Kₕ ⟶ Kₗ :=
  biprod.desc restriction actual.correction

noncomputable def secondCoordinate
    (_actual : TotalFiberShearSuccessorAt high low restriction relative) :
    Kₕ ⊞ Kₕ ⟶ Kₗ :=
  biprod.desc 0 restriction

/-- The unique triangular transition that retains the raw endpoint and
absorbs the relative determinant in the adjugate coordinate. -/
noncomputable def pairTransition
    (actual : TotalFiberShearSuccessorAt high low restriction relative) :
    Kₕ ⊞ Kₕ ⟶ Kₗ ⊞ Kₗ :=
  biprod.lift actual.firstCoordinate actual.secondCoordinate

omit [Limits.HasBinaryBiproducts C] in
theorem correction_action :
    actual.correction ≫ Tₗ =
      restriction ≫ Dₗ ≫ (𝟙 Kₗ - relative) := by
  unfold correction
  have oneSubCommutes :
      (𝟙 Kₗ - relative) ≫ Tₗ = Tₗ ≫ (𝟙 Kₗ - relative) := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id,
      actual.relativeOperatorCommutes]
  calc
    (restriction ≫ Qₗ ≫ (𝟙 Kₗ - relative)) ≫ Tₗ =
        restriction ≫ Qₗ ≫ ((𝟙 Kₗ - relative) ≫ Tₗ) := by
          simp only [Category.assoc]
    _ = restriction ≫ Qₗ ≫ (Tₗ ≫ (𝟙 Kₗ - relative)) := by
      rw [oneSubCommutes]
    _ = restriction ≫ (Qₗ ≫ Tₗ) ≫ (𝟙 Kₗ - relative) := by
      simp only [Category.assoc]
    _ = restriction ≫ Dₗ ≫ (𝟙 Kₗ - relative) := by
      rw [ActionDeterminantAdjugateAt.factorization low]

/-- The shear is an actual arrow square for the two Koszul rows. -/
theorem pairTransition_row_square :
    actual.pairTransition ≫ totalRow Tₗ Dₗ =
      totalRow Tₕ Dₕ ≫ restriction := by
  unfold pairTransition totalRow
  rw [biprod.lift_desc]
  apply biprod.hom_ext'
  · simpa [firstCoordinate, secondCoordinate] using
      actual.operatorSquare.symm
  · have inrFirst :
        (biprod.inr : Kₕ ⟶ Kₕ ⊞ Kₕ) ≫ actual.firstCoordinate =
          actual.correction := by
      simp [firstCoordinate]
    have inrSecond :
        (biprod.inr : Kₕ ⟶ Kₕ ⊞ Kₕ) ≫ actual.secondCoordinate =
          restriction := by
      simp [secondCoordinate]
    have inrHighRow :
        (biprod.inr : Kₕ ⟶ Kₕ ⊞ Kₕ) ≫
            biprod.desc Tₕ (-Dₕ) =
          -Dₕ := by
      simp
    simp only [Preadditive.comp_add, ← Category.assoc]
    rw [inrFirst, inrSecond, inrHighRow]
    rw [actual.correction_action]
    rw [Preadditive.neg_comp, actual.determinantSquare]
    simp only [Preadditive.comp_sub, Category.comp_id,
      Preadditive.comp_neg]
    abel

/-- The same shear sends the high canonical kernel pair to the low one. -/
theorem kernelPair_naturality :
    totalKernelPair Qₕ ≫ actual.pairTransition =
      restriction ≫ totalKernelPair Qₗ := by
  apply biprod.hom_ext
  · simp only [pairTransition, firstCoordinate, secondCoordinate,
      totalKernelPair, Category.assoc, biprod.lift_fst,
      biprod.lift_desc]
    rw [actual.adjugateSquare]
    unfold correction
    simp only [Preadditive.comp_sub,
      Category.comp_id]
    simp only [Category.id_comp]
    abel
  · simp [pairTransition, firstCoordinate, secondCoordinate,
      totalKernelPair]

noncomputable def totalTransition
    (actual : TotalFiberShearSuccessorAt high low restriction relative) :
    TotalFiber Tₕ Dₕ ⟶ TotalFiber Tₗ Dₗ :=
  mappingCoconeMap (totalRow Tₕ Dₕ) (totalRow Tₗ Dₗ)
    actual.pairTransition restriction actual.pairTransition_row_square

/-- The total-fibre successor preserves the generated whole source map. -/
theorem totalInclusion_naturality :
    totalInclusion high ≫ actual.totalTransition =
      restriction ≫ totalInclusion low := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply degree_hom_ext (totalRow Tₗ Dₗ) degree
  · have transitionFst := mappingCoconeMap_fst
      (totalRow Tₕ Dₕ) (totalRow Tₗ Dₗ)
      actual.pairTransition restriction actual.pairTransition_row_square
    have fstEquality :
        (totalInclusion high ≫ actual.totalTransition) ≫
            CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ) =
          (restriction ≫ totalInclusion low) ≫
            CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ) := by
      calc
        (totalInclusion high ≫ actual.totalTransition) ≫
            CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ) =
          totalInclusion high ≫
            (actual.totalTransition ≫
              CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ)) :=
                Category.assoc _ _ _
        _ = totalInclusion high ≫
            (CochainComplex.mappingCocone.fst (totalRow Tₕ Dₕ) ≫
              actual.pairTransition) := by
                unfold totalTransition
                rw [transitionFst]
        _ = (totalInclusion high ≫
              CochainComplex.mappingCocone.fst (totalRow Tₕ Dₕ)) ≫
                actual.pairTransition := (Category.assoc _ _ _).symm
        _ = totalKernelPair Qₕ ≫ actual.pairTransition := by
          rw [totalInclusion_fst]
        _ = restriction ≫ totalKernelPair Qₗ :=
          actual.kernelPair_naturality
        _ = restriction ≫
            (totalInclusion low ≫
              CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ)) := by
                rw [totalInclusion_fst]
        _ = (restriction ≫ totalInclusion low) ≫
            CochainComplex.mappingCocone.fst (totalRow Tₗ Dₗ) :=
              (Category.assoc _ _ _).symm
    exact congrArg (fun arrow ↦ arrow.f degree) fstEquality
  · let previous := degree + (-1)
    have transitionSnd := Cochain.congr_v
      (mappingCoconeMap_snd
        (totalRow Tₕ Dₕ) (totalRow Tₗ Dₗ)
        actual.pairTransition restriction actual.pairTransition_row_square)
      degree previous rfl
    have highSnd :
        (totalInclusion high).f degree ≫
            (CochainComplex.mappingCocone.snd
              (totalRow Tₕ Dₕ)).v degree previous rfl = 0 := by
      simp [totalInclusion]
    have lowSnd :
        (totalInclusion low).f degree ≫
            (CochainComplex.mappingCocone.snd
              (totalRow Tₗ Dₗ)).v degree previous rfl = 0 := by
      simp [totalInclusion]
    have transitionSndComponent :
        actual.totalTransition.f degree ≫
            (CochainComplex.mappingCocone.snd
              (totalRow Tₗ Dₗ)).v degree previous rfl =
          (CochainComplex.mappingCocone.snd
            (totalRow Tₕ Dₕ)).v degree previous rfl ≫
              restriction.f previous := by
      simpa [totalTransition, Cochain.comp_v] using transitionSnd
    simp only [HomologicalComplex.comp_f]
    calc
      ((totalInclusion high).f degree ≫
          actual.totalTransition.f degree) ≫
          (CochainComplex.mappingCocone.snd
            (totalRow Tₗ Dₗ)).v degree previous rfl =
        (totalInclusion high).f degree ≫
          (actual.totalTransition.f degree ≫
            (CochainComplex.mappingCocone.snd
              (totalRow Tₗ Dₗ)).v degree previous rfl) :=
          Category.assoc _ _ _
      _ = (totalInclusion high).f degree ≫
          ((CochainComplex.mappingCocone.snd
            (totalRow Tₕ Dₕ)).v degree previous rfl ≫
              restriction.f previous) := by rw [transitionSndComponent]
      _ = ((totalInclusion high).f degree ≫
          (CochainComplex.mappingCocone.snd
            (totalRow Tₕ Dₕ)).v degree previous rfl) ≫
              restriction.f previous := (Category.assoc _ _ _).symm
      _ = 0 := by rw [highSnd, zero_comp]
      _ = restriction.f degree ≫ 0 := by simp
      _ = restriction.f degree ≫
          ((totalInclusion low).f degree ≫
            (CochainComplex.mappingCocone.snd
              (totalRow Tₗ Dₗ)).v degree previous rfl) := by
                rw [lowSnd]
      _ = (restriction.f degree ≫ (totalInclusion low).f degree) ≫
          (CochainComplex.mappingCocone.snd
            (totalRow Tₗ Dₗ)).v degree previous rfl :=
        (Category.assoc _ _ _).symm

/-- The successor keeps the second/raw endpoint coordinate exactly. -/
theorem pairTransition_second :
    actual.pairTransition ≫ (biprod.snd : Kₗ ⊞ Kₗ ⟶ Kₗ) =
      (biprod.snd : Kₕ ⊞ Kₕ ⟶ Kₕ) ≫ restriction := by
  apply biprod.hom_ext'
  · simp [pairTransition, secondCoordinate]
  · simp [pairTransition, secondCoordinate]

end TotalFiberShearSuccessorAt

end
end CochainMappingCoconeDeterminantAdjugateTotalFiberShearNaturality
end SaturationMonoid
