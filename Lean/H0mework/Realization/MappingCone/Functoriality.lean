import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Functoriality of cochain mapping cocones

A commuting square of cochain maps induces a morphism between their shifted
mapping cocones.  The canonical projection to the source complex is natural
for this morphism.  This file contains no BSD-specific carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainMappingCoconeFunctoriality

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

noncomputable section

/-- Functoriality of the shifted mapping cocone under a commuting square. -/
noncomputable def mappingCoconeMap
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right) :
    CochainComplex.mappingCocone phi ⟶
      CochainComplex.mappingCocone phi' :=
  (CochainComplex.shiftFunctor C (-1)).map
    (homotopyCofiber.mapArrowHom phi phi'
      (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk left right commutes))

set_option backward.isDefEq.respectTransparency false in
private theorem homotopyCofiber_mapArrowHom_sndX
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right)
    (i : ℤ) :
    (homotopyCofiber.mapArrowHom phi phi'
        (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk left right commutes)).f i ≫
        homotopyCofiber.sndX phi' i =
      homotopyCofiber.sndX phi i ≫ right.f i := by
  dsimp [homotopyCofiber.mapArrowHom]
  rw [homotopyCofiber.desc_f _ _ _ i (i + 1) (by simp)]
  simp [Preadditive.add_comp, Category.assoc,
    homotopyCofiber.inrCompHomotopy_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCocone_fst_f
    {C : Type*} [Category* C] [Preadditive C]
    {K L : CochainComplex C ℤ}
    (phi : K ⟶ L) [HasHomotopyCofiber phi] (i : ℤ) :
    (CochainComplex.mappingCocone.fst phi).f i =
      homotopyCofiber.fstX phi (i + -1) i (by simp) := by
  simp only [CochainComplex.mappingCocone.fst,
    CochainComplex.mappingCone.fst,
    HomologicalComplex.neg_f_apply,
    CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.leftShift_coe]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v
    (n := 1) _ (-1) 0 (by norm_num) i i (by simp) (i + -1) (by simp)]
  simp [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCocone_snd_v
    {C : Type*} [Category* C] [Preadditive C]
    {K L : CochainComplex C ℤ}
    (phi : K ⟶ L) [HasHomotopyCofiber phi]
    (p : ℤ) :
    (CochainComplex.mappingCocone.snd phi).v
        p (p + (-1)) rfl =
      ((CochainComplex.mappingCone phi).shiftFunctorObjXIso
          (-1) p (p + (-1)) rfl).hom ≫
        homotopyCofiber.sndX phi (p + (-1)) := by
  unfold CochainComplex.mappingCocone.snd
  rw [CochainComplex.HomComplex.Cochain.leftShift_v
    (CochainComplex.mappingCone.snd phi) (-1) (-1) (zero_add (-1))
      p (p + (-1)) rfl (p + (-1)) (add_zero _)]
  simp [CochainComplex.mappingCone.snd]
  rw [show Int.negOnePow 2 = 1 by rfl, one_smul]

/- The mapping-cocone morphism projects to the left leg of the original
commuting square. -/
set_option backward.isDefEq.respectTransparency false in
theorem mappingCoconeMap_fst
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right) :
    mappingCoconeMap phi phi' left right commutes ≫
        CochainComplex.mappingCocone.fst phi' =
      CochainComplex.mappingCocone.fst phi ≫ left := by
  ext i
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [mappingCoconeMap]
  rw [mappingCocone_fst_f, mappingCocone_fst_f]
  change
    (homotopyCofiber.mapArrowHom phi phi'
        (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk left right commutes)).f (i + -1) ≫
        homotopyCofiber.fstX phi' (i + -1) i (by simp) =
      homotopyCofiber.fstX phi (i + -1) i (by simp) ≫ left.f i
  dsimp [homotopyCofiber.mapArrowHom]
  rw [homotopyCofiber.desc_f _ _ _ (i + -1) i (by simp)]
  simp [homotopyCofiber.inrCompHomotopy_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-minus-one projection is natural for a mapping-cocone map. -/
theorem mappingCoconeMap_snd
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right) :
    (CochainComplex.HomComplex.Cochain.ofHom
        (mappingCoconeMap phi phi' left right commutes)).comp
          (CochainComplex.mappingCocone.snd phi') (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd phi).comp
        (CochainComplex.HomComplex.Cochain.ofHom right) (add_zero (-1)) := by
  ext p q hpq
  obtain rfl : q = p + (-1) := hpq.symm
  rw [CochainComplex.HomComplex.Cochain.comp_v
      _ _ _ p p (p + (-1)) (add_zero p) rfl,
    CochainComplex.HomComplex.Cochain.comp_v
      _ _ _ p (p + (-1)) (p + (-1)) rfl (add_zero _)]
  simp only [CochainComplex.HomComplex.Cochain.ofHom_v]
  rw [mappingCocone_snd_v, mappingCocone_snd_v]
  unfold mappingCoconeMap
  dsimp only [CochainComplex.shiftFunctor,
    CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq]
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  change
    (homotopyCofiber.mapArrowHom phi phi'
        (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk left right commutes)).f (p + (-1)) ≫
          homotopyCofiber.sndX phi' (p + (-1)) =
      homotopyCofiber.sndX phi (p + (-1)) ≫ right.f (p + (-1))
  exact homotopyCofiber_mapArrowHom_sndX
    phi phi' left right commutes (p + (-1))

/- Equality of the two square legs determines the induced cocone map;
commutativity witnesses carry no extra data. -/
theorem mappingCoconeMap_congr
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    {left left' : K ⟶ K'} {right right' : L ⟶ L'}
    (commutes : left ≫ phi' = phi ≫ right)
    (commutes' : left' ≫ phi' = phi ≫ right')
    (left_eq : left = left') (right_eq : right = right') :
    mappingCoconeMap phi phi' left right commutes =
      mappingCoconeMap phi phi' left' right' commutes' := by
  subst left'
  subst right'
  rfl

/- Identity squares induce the identity mapping-cocone morphism. -/
set_option backward.isDefEq.respectTransparency false in
theorem mappingCoconeMap_id
    {C : Type*} [Category* C] [Preadditive C]
    {K L : CochainComplex C ℤ}
    (phi : K ⟶ L) [HasHomotopyCofiber phi] :
    mappingCoconeMap phi phi (𝟙 _) (𝟙 _) (by simp) = 𝟙 _ := by
  unfold mappingCoconeMap
  rw [show Arrow.homMk (𝟙 K) (𝟙 L) (by simp) =
      𝟙 (Arrow.mk phi) by
    ext <;> simp]
  rw [homotopyCofiber.mapArrowHom_id]
  change (CochainComplex.shiftFunctor C (-1)).map
      (𝟙 (CochainComplex.mappingCone phi)) =
    𝟙 ((CochainComplex.shiftFunctor C (-1)).obj
      (CochainComplex.mappingCone phi))
  exact (CochainComplex.shiftFunctor C (-1)).map_id
    (CochainComplex.mappingCone phi)

/- Composition of commuting squares is preserved by the mapping-cocone
construction. -/
set_option backward.isDefEq.respectTransparency false in
theorem mappingCoconeMap_comp
    {C : Type*} [Category* C] [Preadditive C]
    {K L K' L' K'' L'' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L') (phi'' : K'' ⟶ L'')
    [HasHomotopyCofiber phi] [HasHomotopyCofiber phi']
    [HasHomotopyCofiber phi'']
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right)
    (left' : K' ⟶ K'') (right' : L' ⟶ L'')
    (commutes' : left' ≫ phi'' = phi' ≫ right') :
    mappingCoconeMap phi phi'' (left ≫ left') (right ≫ right')
        (by rw [Category.assoc, commutes', ← Category.assoc,
          commutes, Category.assoc]) =
      mappingCoconeMap phi phi' left right commutes ≫
        mappingCoconeMap phi' phi'' left' right' commutes' := by
  unfold mappingCoconeMap
  rw [← Functor.map_comp]
  apply congrArg
  rw [← homotopyCofiber.mapArrowHom_comp]
  congr 1

end

end CochainMappingCoconeFunctoriality
end SaturationMonoid
