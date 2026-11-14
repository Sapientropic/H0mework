import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The kernel of an epimorphism as its mapping cocone

A short exact sequence generates the canonical kernel-to-mapping-cocone
quasi-isomorphism. The actual zero composite supplies its chain lift;
an explicit mapping-cone homotopy and the derived triangle five-lemma
prove the comparison without choosing a section of the epimorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex CochainComplex CochainComplex.HomComplex

namespace SaturationMonoid.CochainMappingCoconeShortExact

noncomputable section

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex (CochainComplex C ℤ))

/-- The zero composite determines this chain map without a splitting. -/
def liftShortComplex : S.X₁ ⟶ CochainComplex.mappingCocone S.g :=
  CochainComplex.mappingCocone.lift S.g S.f 0 (by simp [S.zero])

@[reassoc (attr := simp)] theorem liftShortComplex_fst :
    liftShortComplex S ≫ CochainComplex.mappingCocone.fst S.g = S.f := by
  simp [liftShortComplex]

private def nullSquareMap : CochainComplex.mappingCone S.f ⟶
    CochainComplex.mappingCone S.g :=
  CochainComplex.mappingCone.map S.f S.g S.f 0 (by simp [S.zero])

private def nullSquareHomotopy : Homotopy (nullSquareMap S)
    (-(CochainComplex.mappingCone.descShortComplex S ≫
        CochainComplex.mappingCone.inr S.g)) := by
  apply CochainComplex.mappingCone.descHomotopy S.f _ _ 0
    (CochainComplex.mappingCone.inl S.g)
  · ext p q hpq
    simp [nullSquareMap, CochainComplex.mappingCone.map]
  · simp [nullSquareMap, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.δ_inl]

private theorem shifted_lift_eq :
    (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        (liftShortComplex S)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).hom.app
          (CochainComplex.mappingCone S.g) =
      -(nullSquareMap S) := by
  ext p
  apply CochainComplex.mappingCone.ext_from S.f (p + 1) p rfl
  · simp [CochainComplex.mappingCone.triangle, liftShortComplex,
      CochainComplex.mappingCocone.lift, CochainComplex.mappingCocone.liftCochain,
      CochainComplex.mappingCone.liftCochain,
      CochainComplex.HomComplex.Cochain.rightShift_v,
      shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f',
      shiftFunctorZero_hom_app_f, nullSquareMap,
      CochainComplex.mappingCone.map]
  · simp [nullSquareMap, CochainComplex.mappingCone.map]

attribute [local instance] HasDerivedCategory.standard

private theorem derived_second :
    DerivedCategory.Q.map ((CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        (liftShortComplex S)⟦(1 : ℤ)⟧') =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S ≫
        (CochainComplex.mappingCocone.triangle S.g).mor₃) := by
  let j := (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).hom.app
    (CochainComplex.mappingCone S.g)
  apply (cancel_mono (DerivedCategory.Q.map j)).mp
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [Category.assoc, shifted_lift_eq]
  have h : Homotopy (-(nullSquareMap S))
      (CochainComplex.mappingCone.descShortComplex S ≫
        CochainComplex.mappingCone.inr S.g) := by
    simpa only [neg_one_smul, neg_neg] using
      (nullSquareHomotopy S).smul (-1 : ℤ)
  rw [DerivedCategory.Q_map_eq_of_homotopy C h]
  congr 1
  simp [j, CochainComplex.mappingCocone.triangle, Category.assoc]

private def triangleMap :
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f).rotate ⟶
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle S.g).rotate where
  hom₁ := DerivedCategory.Q.map (𝟙 _)
  hom₂ := DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)
  hom₃ := DerivedCategory.Q.map ((liftShortComplex S)⟦(1 : ℤ)⟧')
  comm₁ := by simp [← Functor.map_comp]
  comm₂ := by
    change DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        DerivedCategory.Q.map ((liftShortComplex S)⟦(1 : ℤ)⟧') =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S) ≫
        DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle S.g).mor₃
    simpa only [← Functor.map_comp] using derived_second S
  comm₃ := by
    change
      (DerivedCategory.Q.map (-(S.f⟦(1 : ℤ)⟧')) ≫
          (Functor.commShiftIso DerivedCategory.Q (1 : ℤ)).hom.app S.X₂) ≫
          (DerivedCategory.Q.map (𝟙 S.X₂))⟦(1 : ℤ)⟧' =
        DerivedCategory.Q.map ((liftShortComplex S)⟦(1 : ℤ)⟧') ≫
          (DerivedCategory.Q.map (-((CochainComplex.mappingCocone.fst S.g)⟦(1 : ℤ)⟧')) ≫
            (Functor.commShiftIso DerivedCategory.Q (1 : ℤ)).hom.app S.X₂)
    simp only [Functor.map_neg,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    simp [liftShortComplex_fst]

private theorem map_rotate_distinguished
    (T : Triangle (CochainComplex C ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _) :
    DerivedCategory.Q.mapTriangle.obj T.rotate ∈ distTriang _ :=
  isomorphic_distinguished _ (rot_of_distTriang _ hT) _
    (DerivedCategory.Q.mapTriangleRotateIso.app T).symm

/-- Exactness alone identifies the kernel complex with the homotopy fibre. -/
theorem quasiIso_liftShortComplex (hS : S.ShortExact) :
    QuasiIso (liftShortComplex S) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hi := isIso₃_of_isIso₁₂ (triangleMap S)
    (map_rotate_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished S.f))
    (map_rotate_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished S.g))
    (by dsimp [triangleMap]; infer_instance)
    (by dsimp [triangleMap]; infer_instance)
  have hq : QuasiIso ((liftShortComplex S)⟦(1 : ℤ)⟧') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C _).mp hi
  exact (CochainComplex.quasiIso_shift_iff _ 1).mp hq

end
end SaturationMonoid.CochainMappingCoconeShortExact
