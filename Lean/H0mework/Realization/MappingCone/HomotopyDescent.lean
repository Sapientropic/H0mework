import H0mework.Realization.MappingCone.Functoriality
import H0mework.Realization.MappingCone.Degreewise
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Homotopy-coherent descent through mapping cocones

Endpoint homotopies and their actual two-cell generate the induced homotopy
between mapping-cocone maps. No cone homotopy is supplied by the caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

open CategoryTheory

noncomputable section

namespace MappingCoconeHomotopyDescent

open CochainComplex.HomComplex
open HomologicalComplex

variable {K L : CochainComplex (ModuleCat ℤ) ℤ}
variable (arrow : K ⟶ L)

theorem mappingCocone_delta_inl :
    δ 0 1 (CochainComplex.mappingCocone.inl arrow) =
      -((Cochain.ofHom arrow).comp
        (CochainComplex.mappingCocone.inr arrow).1 (zero_add 1)) := by
  dsimp [CochainComplex.mappingCocone.inl,
    CochainComplex.mappingCocone.inr]
  simp [Cochain.δ_rightShift, CochainComplex.mappingCone.δ_inl]
  ext sourceDegree targetDegree degree_eq : 1
  simp [Cochain.rightShift_v]

theorem mappingCoconeMap_inl
    (left : K ⟶ K) (right : L ⟶ L)
    (square : left ≫ arrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inl arrow).comp
        (Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square)) (zero_add 0) =
      (Cochain.ofHom left).comp
        (CochainComplex.mappingCocone.inl arrow) (zero_add 0) := by
  ext sourceDegree : 1
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext arrow sourceDegree
  · simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Category.assoc]
    have generated := congrArg (fun map ↦ map.f sourceDegree)
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
        arrow arrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [generated]
    simp
  · simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Category.assoc]
    have generated := Cochain.congr_v
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
        arrow arrow left right square)
      sourceDegree (sourceDegree + (-1)) rfl
    have generatedComponent :
        (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square).f sourceDegree ≫
            (CochainComplex.mappingCocone.snd arrow).v
              sourceDegree (sourceDegree + (-1)) rfl =
          (CochainComplex.mappingCocone.snd arrow).v
              sourceDegree (sourceDegree + (-1)) rfl ≫
            right.f (sourceDegree + (-1)) := by
      simpa [Cochain.comp_v] using generated
    rw [generatedComponent]
    simp

theorem mappingCoconeMap_inr
    (left : K ⟶ K) (right : L ⟶ L)
    (square : left ≫ arrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inr arrow).1.comp
        (Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square)) (add_zero 1) =
      (Cochain.ofHom right).comp
        (CochainComplex.mappingCocone.inr arrow).1 (zero_add 1) := by
  ext sourceDegree targetDegree degree_eq : 1
  rw [Cochain.comp_v _ _ (add_zero 1)
      sourceDegree targetDegree targetDegree degree_eq
        (add_zero targetDegree),
    Cochain.comp_v _ _ (zero_add 1)
      sourceDegree sourceDegree targetDegree
        (add_zero sourceDegree) degree_eq]
  simp only [Cochain.ofHom_v]
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext_at
    arrow targetDegree sourceDegree (by omega)
  · have generated := congrArg (fun map ↦ map.f targetDegree)
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
        arrow arrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [Category.assoc, generated]
    simp
  · have generated := Cochain.congr_v
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
        arrow arrow left right square)
      targetDegree sourceDegree (by omega)
    have generatedComponent :
        (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow left right square).f targetDegree ≫
            (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) =
          (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) ≫
            right.f sourceDegree := by
      simpa [Cochain.comp_v] using generated
    rw [Category.assoc, generatedComponent]
    simp [Category.assoc]

theorem mappingCoconeMap_inl_between
    {K' L' : CochainComplex (ModuleCat ℤ) ℤ}
    (targetArrow : K' ⟶ L')
    (left : K ⟶ K') (right : L ⟶ L')
    (square : left ≫ targetArrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inl arrow).comp
        (Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow left right square)) (zero_add 0) =
      (Cochain.ofHom left).comp
        (CochainComplex.mappingCocone.inl targetArrow) (zero_add 0) := by
  ext sourceDegree : 1
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext
    targetArrow sourceDegree
  · simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Category.assoc]
    have generated := congrArg (fun map ↦ map.f sourceDegree)
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
        arrow targetArrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [generated]
    simp
  · simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Category.assoc]
    have generated := Cochain.congr_v
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
        arrow targetArrow left right square)
      sourceDegree (sourceDegree + (-1)) rfl
    have generatedComponent :
        (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow left right square).f sourceDegree ≫
            (CochainComplex.mappingCocone.snd targetArrow).v
              sourceDegree (sourceDegree + (-1)) rfl =
          (CochainComplex.mappingCocone.snd arrow).v
              sourceDegree (sourceDegree + (-1)) rfl ≫
            right.f (sourceDegree + (-1)) := by
      simpa [Cochain.comp_v] using generated
    rw [generatedComponent]
    simp

theorem mappingCoconeMap_inr_between
    {K' L' : CochainComplex (ModuleCat ℤ) ℤ}
    (targetArrow : K' ⟶ L')
    (left : K ⟶ K') (right : L ⟶ L')
    (square : left ≫ targetArrow = arrow ≫ right) :
    (CochainComplex.mappingCocone.inr arrow).1.comp
        (Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow left right square)) (add_zero 1) =
      (Cochain.ofHom right).comp
        (CochainComplex.mappingCocone.inr targetArrow).1
        (zero_add 1) := by
  ext sourceDegree targetDegree degree_eq : 1
  rw [Cochain.comp_v _ _ (add_zero 1)
      sourceDegree targetDegree targetDegree degree_eq
        (add_zero targetDegree),
    Cochain.comp_v _ _ (zero_add 1)
      sourceDegree sourceDegree targetDegree
        (add_zero sourceDegree) degree_eq]
  simp only [Cochain.ofHom_v]
  apply CochainMappingCoconeDegreewiseKernel.degree_hom_ext_at
    targetArrow targetDegree sourceDegree (by omega)
  · have generated := congrArg (fun map ↦ map.f targetDegree)
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
        arrow targetArrow left right square)
    simp only [HomologicalComplex.comp_f] at generated
    rw [Category.assoc, generated]
    simp
  · have generated := Cochain.congr_v
      (CochainMappingCoconeFunctoriality.mappingCoconeMap_snd
        arrow targetArrow left right square)
      targetDegree sourceDegree (by omega)
    have generatedComponent :
        (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow left right square).f targetDegree ≫
            (CochainComplex.mappingCocone.snd targetArrow).v
              targetDegree sourceDegree (by omega) =
          (CochainComplex.mappingCocone.snd arrow).v
              targetDegree sourceDegree (by omega) ≫
            right.f sourceDegree := by
      simpa [Cochain.comp_v] using generated
    rw [Category.assoc, generatedComponent]
    simp [Category.assoc]

theorem mappingCocone_cochain_ext
    {M : CochainComplex (ModuleCat ℤ) ℤ} {degree : ℤ}
    {left right : Cochain (CochainComplex.mappingCocone arrow) M degree}
    (inl_eq :
      (CochainComplex.mappingCocone.inl arrow).comp left
          (zero_add degree) =
        (CochainComplex.mappingCocone.inl arrow).comp right
          (zero_add degree))
    (inr_eq :
      (CochainComplex.mappingCocone.inr arrow).1.comp left
          (show 1 + degree = degree + 1 by omega) =
        (CochainComplex.mappingCocone.inr arrow).1.comp right
          (show 1 + degree = degree + 1 by omega)) :
    left = right := by
  ext sourceDegree targetDegree degree_eq : 1
  let previousDegree := sourceDegree + (-1)
  have source_previous : sourceDegree + (-1) = previousDegree := rfl
  have previous_source : previousDegree + 1 = sourceDegree := by
    dsimp [previousDegree]
    omega
  rw [← Category.id_comp (left.v sourceDegree targetDegree degree_eq),
    ← Category.id_comp (right.v sourceDegree targetDegree degree_eq),
    ← CochainComplex.mappingCocone.id_X
      arrow sourceDegree previousDegree source_previous]
  simp only [Preadditive.add_comp, Category.assoc]
  apply congrArg₂ (fun first second ↦ first + second)
  · have generated := Cochain.congr_v inl_eq
      sourceDegree targetDegree degree_eq
    have generatedComponent :
        (CochainComplex.mappingCocone.inl arrow).v
            sourceDegree sourceDegree (add_zero sourceDegree) ≫
            left.v sourceDegree targetDegree degree_eq =
          (CochainComplex.mappingCocone.inl arrow).v
            sourceDegree sourceDegree (add_zero sourceDegree) ≫
            right.v sourceDegree targetDegree degree_eq := by
      simpa [Cochain.comp_v] using generated
    simpa [Category.assoc] using congrArg
      (fun map ↦ (CochainComplex.mappingCocone.fst arrow).f
        sourceDegree ≫ map) generatedComponent
  · have generated := Cochain.congr_v inr_eq
      previousDegree targetDegree (by
        rw [← degree_eq]
        dsimp [previousDegree]
        omega)
    have generatedComponent :
        (CochainComplex.mappingCocone.inr arrow).1.v
            previousDegree sourceDegree previous_source ≫
            left.v sourceDegree targetDegree degree_eq =
          (CochainComplex.mappingCocone.inr arrow).1.v
            previousDegree sourceDegree previous_source ≫
            right.v sourceDegree targetDegree degree_eq := by
      rw [Cochain.comp_v _ _ _
          previousDegree sourceDegree targetDegree
            previous_source degree_eq,
        Cochain.comp_v _ _ _
          previousDegree sourceDegree targetDegree
            previous_source degree_eq] at generated
      exact generated
    simpa [Category.assoc] using congrArg
      (fun map ↦ (CochainComplex.mappingCocone.snd arrow).v
        sourceDegree previousDegree source_previous ≫ map)
      generatedComponent

noncomputable def mappingCoconeHomotopyCochain
    (sourceAction : K ⟶ K) (targetAction : L ⟶ L)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K))
    (targetHomotopy : Homotopy targetAction (𝟙 L)) :
    Cochain (CochainComplex.mappingCocone arrow)
      (CochainComplex.mappingCocone arrow) (-1) :=
  CochainComplex.mappingCocone.descCochain arrow
    ((Cochain.ofHomotopy sourceHomotopy).comp
      (CochainComplex.mappingCocone.inl arrow) (add_zero (-1)))
    (-((Cochain.ofHomotopy targetHomotopy).comp
      (CochainComplex.mappingCocone.inr arrow).1 (neg_add_cancel 1)))
    (neg_add_cancel 1)

theorem mappingCocone_sourceHomotopyPart_delta
    (sourceAction : K ⟶ K)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K)) :
    δ (-1) 0
        ((Cochain.ofHomotopy sourceHomotopy).comp
          (CochainComplex.mappingCocone.inl arrow) (add_zero (-1))) =
      -(((Cochain.ofHomotopy sourceHomotopy).comp
          (Cochain.ofHom arrow) (add_zero (-1))).comp
        (CochainComplex.mappingCocone.inr arrow).1 (neg_add_cancel 1)) +
      (Cochain.ofHom sourceAction - Cochain.ofHom (𝟙 K)).comp
        (CochainComplex.mappingCocone.inl arrow) (add_zero 0) := by
  rw [δ_comp_zero_cochain]
  rw [mappingCocone_delta_inl, δ_ofHomotopy]
  ext sourceDegree : 1
  simp [Cochain.comp_v]
  all_goals norm_num

theorem mappingCocone_targetHomotopyPart_delta
    (targetAction : L ⟶ L)
    (targetHomotopy : Homotopy targetAction (𝟙 L)) :
    δ 0 1
        (-((Cochain.ofHomotopy targetHomotopy).comp
          (CochainComplex.mappingCocone.inr arrow).1
          (neg_add_cancel 1))) =
      (Cochain.ofHom targetAction - Cochain.ofHom (𝟙 L)).comp
        (CochainComplex.mappingCocone.inr arrow).1 (zero_add 1) := by
  rw [δ_neg]
  rw [δ_comp _ _ (neg_add_cancel 1) 0 2 1
    (zero_add 1) (neg_add_cancel 1) (by omega)]
  have inrClosed :
      δ 1 2 (CochainComplex.mappingCocone.inr arrow).1 = 0 :=
    (Cocycle.mem_iff (F := L)
      (G := CochainComplex.mappingCocone arrow)
      (n := 1) (m := 2) (by omega)
      (CochainComplex.mappingCocone.inr arrow).1).mp
        (CochainComplex.mappingCocone.inr arrow).2
  rw [inrClosed, δ_ofHomotopy]
  ext sourceDegree targetDegree degree_eq : 1
  simp

theorem mappingCoconeHomotopyCochain_delta
    (sourceAction : K ⟶ K) (targetAction : L ⟶ L)
    (square : sourceAction ≫ arrow = arrow ≫ targetAction)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K))
    (targetHomotopy : Homotopy targetAction (𝟙 L))
    (twoCell :
      Cochain.ofHomotopy (sourceHomotopy.compRight arrow) =
        Cochain.ofHomotopy (targetHomotopy.compLeft arrow)) :
    δ (-1) 0
        (mappingCoconeHomotopyCochain arrow sourceAction targetAction
          sourceHomotopy targetHomotopy) =
      Cochain.ofHom
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow arrow sourceAction targetAction square) -
        Cochain.ofHom (𝟙 _) := by
  unfold mappingCoconeHomotopyCochain
  rw [CochainComplex.mappingCocone.δ_descCochain
    arrow _ _ _ 1 (zero_add 1)]
  rw [mappingCocone_sourceHomotopyPart_delta,
    mappingCocone_targetHomotopyPart_delta]
  apply mappingCocone_cochain_ext arrow
  · ext sourceDegree : 1
    simp [Cochain.comp_v, mappingCoconeMap_inl]
    have generated := Cochain.congr_v twoCell
      sourceDegree (sourceDegree + (-1)) rfl
    have generatedComponent :
        (Cochain.ofHomotopy sourceHomotopy).v
            sourceDegree (sourceDegree + (-1)) rfl ≫
            arrow.f (sourceDegree + (-1)) =
          arrow.f sourceDegree ≫
            (Cochain.ofHomotopy targetHomotopy).v
              sourceDegree (sourceDegree + (-1)) rfl := by
      simpa only [Cochain.ofHomotopy, Cochain.mk_v,
        Homotopy.compRight_hom, Homotopy.compLeft_hom] using generated
    have generatedRouted := congrArg
      (fun map ↦ map ≫
        (CochainComplex.mappingCocone.inr arrow).1.v
          (sourceDegree + (-1)) sourceDegree (by omega))
      generatedComponent
    simp only [Category.assoc] at generatedRouted
    rw [generatedRouted]
    abel
  · ext sourceDegree targetDegree degree_eq : 1
    obtain rfl : targetDegree = sourceDegree + 1 := by omega
    simp [Cochain.comp_v, ← Category.assoc, mappingCoconeMap_inr]

noncomputable def mappingCoconeMapHomotopy
    (sourceAction : K ⟶ K) (targetAction : L ⟶ L)
    (square : sourceAction ≫ arrow = arrow ≫ targetAction)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K))
    (targetHomotopy : Homotopy targetAction (𝟙 L))
    (twoCell :
      Cochain.ofHomotopy (sourceHomotopy.compRight arrow) =
        Cochain.ofHomotopy (targetHomotopy.compLeft arrow)) :
    Homotopy
      (CochainMappingCoconeFunctoriality.mappingCoconeMap
        arrow arrow sourceAction targetAction square)
      (𝟙 _) :=
  (Cochain.equivHomotopy
    (CochainMappingCoconeFunctoriality.mappingCoconeMap
      arrow arrow sourceAction targetAction square) (𝟙 _)).symm
    ⟨mappingCoconeHomotopyCochain arrow sourceAction targetAction
        sourceHomotopy targetHomotopy,
      by
        rw [mappingCoconeHomotopyCochain_delta
          arrow sourceAction targetAction square sourceHomotopy
            targetHomotopy twoCell]
        abel⟩

theorem mappingCoconeMapHomotopy_cochain
    (sourceAction : K ⟶ K) (targetAction : L ⟶ L)
    (square : sourceAction ≫ arrow = arrow ≫ targetAction)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K))
    (targetHomotopy : Homotopy targetAction (𝟙 L))
    (twoCell :
      Cochain.ofHomotopy (sourceHomotopy.compRight arrow) =
        Cochain.ofHomotopy (targetHomotopy.compLeft arrow)) :
    Cochain.ofHomotopy
        (mappingCoconeMapHomotopy arrow sourceAction targetAction square
          sourceHomotopy targetHomotopy twoCell) =
      mappingCoconeHomotopyCochain arrow sourceAction targetAction
        sourceHomotopy targetHomotopy := by
  let action := CochainMappingCoconeFunctoriality.mappingCoconeMap
    arrow arrow sourceAction targetAction square
  let cochain := mappingCoconeHomotopyCochain arrow
    sourceAction targetAction sourceHomotopy targetHomotopy
  let witness :
      { z : Cochain (CochainComplex.mappingCocone arrow)
          (CochainComplex.mappingCocone arrow) (-1) //
        Cochain.ofHom action = δ (-1) 0 z + Cochain.ofHom (𝟙 _) } :=
    ⟨cochain, by
      dsimp [action, cochain]
      rw [mappingCoconeHomotopyCochain_delta
        arrow sourceAction targetAction square sourceHomotopy
          targetHomotopy twoCell]
      abel⟩
  change Cochain.ofHomotopy
      ((Cochain.equivHomotopy action (𝟙 _)).symm witness) = cochain
  exact congrArg Subtype.val
    ((Cochain.equivHomotopy action (𝟙 _)).apply_symm_apply witness)

theorem ofHomotopy_compRight
    {A B C : CochainComplex (ModuleCat ℤ) ℤ}
    {left right : A ⟶ B} (homotopy : Homotopy left right)
    (map : B ⟶ C) :
    Cochain.ofHomotopy (homotopy.compRight map) =
      (Cochain.ofHomotopy homotopy).comp
        (Cochain.ofHom map) (add_zero (-1)) := by
  ext sourceDegree targetDegree degree_eq : 1
  change homotopy.hom sourceDegree targetDegree ≫ map.f targetDegree = _
  rw [Cochain.comp_v _ _ (add_zero (-1))
    sourceDegree targetDegree targetDegree degree_eq
      (add_zero targetDegree)]
  rfl

theorem ofHomotopy_compLeft
    {A B C : CochainComplex (ModuleCat ℤ) ℤ}
    {left right : B ⟶ C} (homotopy : Homotopy left right)
    (map : A ⟶ B) :
    Cochain.ofHomotopy (homotopy.compLeft map) =
      (Cochain.ofHom map).comp
        (Cochain.ofHomotopy homotopy) (zero_add (-1)) := by
  ext sourceDegree targetDegree degree_eq : 1
  change map.f sourceDegree ≫ homotopy.hom
    sourceDegree targetDegree = _
  rw [Cochain.comp_v _ _ (zero_add (-1))
    sourceDegree sourceDegree targetDegree (add_zero sourceDegree)
      degree_eq]
  rfl

theorem mappingCoconeMapHomotopy_naturality
    {K' L' : CochainComplex (ModuleCat ℤ) ℤ}
    (targetArrow : K' ⟶ L')
    (sourceAction : K ⟶ K) (targetAction : L ⟶ L)
    (actionSquare : sourceAction ≫ arrow = arrow ≫ targetAction)
    (sourceHomotopy : Homotopy sourceAction (𝟙 K))
    (targetHomotopy : Homotopy targetAction (𝟙 L))
    (actionTwoCell :
      Cochain.ofHomotopy (sourceHomotopy.compRight arrow) =
        Cochain.ofHomotopy (targetHomotopy.compLeft arrow))
    (sourceAction' : K' ⟶ K') (targetAction' : L' ⟶ L')
    (actionSquare' :
      sourceAction' ≫ targetArrow = targetArrow ≫ targetAction')
    (sourceHomotopy' : Homotopy sourceAction' (𝟙 K'))
    (targetHomotopy' : Homotopy targetAction' (𝟙 L'))
    (actionTwoCell' :
      Cochain.ofHomotopy (sourceHomotopy'.compRight targetArrow) =
        Cochain.ofHomotopy (targetHomotopy'.compLeft targetArrow))
    (sourceTransition : K ⟶ K') (targetTransition : L ⟶ L')
    (transitionSquare :
      sourceTransition ≫ targetArrow = arrow ≫ targetTransition)
    (sourceHomotopyTwoCell :
      Cochain.ofHomotopy
          (sourceHomotopy.compRight sourceTransition) =
        Cochain.ofHomotopy
          (sourceHomotopy'.compLeft sourceTransition))
    (targetHomotopyTwoCell :
      Cochain.ofHomotopy
          (targetHomotopy.compRight targetTransition) =
        Cochain.ofHomotopy
          (targetHomotopy'.compLeft targetTransition)) :
    Cochain.ofHomotopy
        ((mappingCoconeMapHomotopy arrow sourceAction targetAction
          actionSquare sourceHomotopy targetHomotopy actionTwoCell).compRight
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow sourceTransition targetTransition
              transitionSquare)) =
      Cochain.ofHomotopy
        ((mappingCoconeMapHomotopy targetArrow sourceAction' targetAction'
          actionSquare' sourceHomotopy' targetHomotopy'
            actionTwoCell').compLeft
          (CochainMappingCoconeFunctoriality.mappingCoconeMap
            arrow targetArrow sourceTransition targetTransition
              transitionSquare)) := by
  rw [ofHomotopy_compRight, ofHomotopy_compLeft,
    mappingCoconeMapHomotopy_cochain,
    mappingCoconeMapHomotopy_cochain]
  apply mappingCocone_cochain_ext arrow
  · ext sourceDegree targetDegree degree_eq : 1
    simp [mappingCoconeHomotopyCochain]
    have transitionInl (degree : ℤ) :
        (CochainComplex.mappingCocone.inl arrow).v
            degree degree (add_zero degree) ≫
            (CochainMappingCoconeFunctoriality.mappingCoconeMap
              arrow targetArrow sourceTransition targetTransition
                transitionSquare).f degree =
          sourceTransition.f degree ≫
            (CochainComplex.mappingCocone.inl targetArrow).v
              degree degree (add_zero degree) := by
      have generated := Cochain.congr_v
        (mappingCoconeMap_inl_between arrow targetArrow
          sourceTransition targetTransition transitionSquare)
        degree degree (add_zero degree)
      simpa [Cochain.comp_v] using generated
    have lowDesc :
        (CochainComplex.mappingCocone.inl targetArrow).v
            sourceDegree sourceDegree (add_zero sourceDegree) ≫
            (CochainComplex.mappingCocone.descCochain targetArrow
              ((Cochain.ofHomotopy sourceHomotopy').comp
                (CochainComplex.mappingCocone.inl targetArrow)
                  (add_zero (-1)))
              (-((Cochain.ofHomotopy targetHomotopy').comp
                (CochainComplex.mappingCocone.inr targetArrow).1
                  (neg_add_cancel 1)))
              (neg_add_cancel 1)).v
                sourceDegree targetDegree degree_eq =
          (Cochain.ofHomotopy sourceHomotopy').v
            sourceDegree targetDegree degree_eq ≫
          (CochainComplex.mappingCocone.inl targetArrow).v
            targetDegree targetDegree (add_zero targetDegree) := by
      have generated :=
        CochainComplex.mappingCocone.inl_v_descCochain_v
        targetArrow
          (α := (Cochain.ofHomotopy sourceHomotopy').comp
            (CochainComplex.mappingCocone.inl targetArrow)
              (add_zero (-1)))
          (β := -((Cochain.ofHomotopy targetHomotopy').comp
            (CochainComplex.mappingCocone.inr targetArrow).1
              (neg_add_cancel 1)))
          (h := neg_add_cancel 1)
          sourceDegree targetDegree degree_eq
      rw [Cochain.comp_v _ _ (add_zero (-1))
        sourceDegree targetDegree targetDegree degree_eq
          (add_zero targetDegree)] at generated
      exact generated
    have generated := Cochain.congr_v sourceHomotopyTwoCell
      sourceDegree targetDegree degree_eq
    have generatedComponent :
        (Cochain.ofHomotopy sourceHomotopy).v
            sourceDegree targetDegree degree_eq ≫
            sourceTransition.f targetDegree =
          sourceTransition.f sourceDegree ≫
            (Cochain.ofHomotopy sourceHomotopy').v
              sourceDegree targetDegree degree_eq := by
      simpa only [Cochain.ofHomotopy, Cochain.mk_v,
        Homotopy.compRight_hom, Homotopy.compLeft_hom] using generated
    rw [transitionInl targetDegree]
    conv_rhs => rw [← Category.assoc]
    rw [transitionInl sourceDegree, Category.assoc, lowDesc]
    simpa [Category.assoc] using congrArg
      (fun map ↦ map ≫
        (CochainComplex.mappingCocone.inl targetArrow).v
          targetDegree targetDegree (add_zero targetDegree))
      generatedComponent
  · ext sourceDegree : 1
    rename_i targetDegree degree_eq
    obtain rfl : targetDegree = sourceDegree := by omega
    unfold mappingCoconeHomotopyCochain
    rw [Cochain.comp_v _ _ (show 1 + (-1) = 0 by omega)
        targetDegree (targetDegree + 1) targetDegree rfl (by omega),
      Cochain.comp_v _ _ (add_zero (-1))
        (targetDegree + 1) targetDegree targetDegree
          (by omega) (add_zero targetDegree),
      Cochain.comp_v _ _ (show 1 + (-1) = 0 by omega)
        targetDegree (targetDegree + 1) targetDegree rfl (by omega),
      Cochain.comp_v _ _ (zero_add (-1))
        (targetDegree + 1) (targetDegree + 1) targetDegree
          (add_zero (targetDegree + 1)) (by omega)]
    simp only [Cochain.ofHom_v]
    have highDesc :
        (CochainComplex.mappingCocone.inr arrow).1.v
            targetDegree (targetDegree + 1) rfl ≫
            (CochainComplex.mappingCocone.descCochain arrow
              ((Cochain.ofHomotopy sourceHomotopy).comp
                (CochainComplex.mappingCocone.inl arrow)
                  (add_zero (-1)))
              (-((Cochain.ofHomotopy targetHomotopy).comp
                (CochainComplex.mappingCocone.inr arrow).1
                  (neg_add_cancel 1)))
              (neg_add_cancel 1)).v
                (targetDegree + 1) targetDegree (by omega) =
          (-((Cochain.ofHomotopy targetHomotopy).comp
            (CochainComplex.mappingCocone.inr arrow).1
              (neg_add_cancel 1))).v
            targetDegree targetDegree (add_zero targetDegree) := by
      exact CochainComplex.mappingCocone.inr_v_descCochain_v
        arrow
          (α := (Cochain.ofHomotopy sourceHomotopy).comp
            (CochainComplex.mappingCocone.inl arrow)
              (add_zero (-1)))
          (β := -((Cochain.ofHomotopy targetHomotopy).comp
            (CochainComplex.mappingCocone.inr arrow).1
              (neg_add_cancel 1)))
          (h := neg_add_cancel 1)
          targetDegree (targetDegree + 1) rfl
            targetDegree (by omega)
    have lowDesc :
        (CochainComplex.mappingCocone.inr targetArrow).1.v
            targetDegree (targetDegree + 1) rfl ≫
            (CochainComplex.mappingCocone.descCochain targetArrow
              ((Cochain.ofHomotopy sourceHomotopy').comp
                (CochainComplex.mappingCocone.inl targetArrow)
                  (add_zero (-1)))
              (-((Cochain.ofHomotopy targetHomotopy').comp
                (CochainComplex.mappingCocone.inr targetArrow).1
                  (neg_add_cancel 1)))
              (neg_add_cancel 1)).v
                (targetDegree + 1) targetDegree (by omega) =
          (-((Cochain.ofHomotopy targetHomotopy').comp
            (CochainComplex.mappingCocone.inr targetArrow).1
              (neg_add_cancel 1))).v
            targetDegree targetDegree (add_zero targetDegree) := by
      exact CochainComplex.mappingCocone.inr_v_descCochain_v
        targetArrow
          (α := (Cochain.ofHomotopy sourceHomotopy').comp
            (CochainComplex.mappingCocone.inl targetArrow)
              (add_zero (-1)))
          (β := -((Cochain.ofHomotopy targetHomotopy').comp
            (CochainComplex.mappingCocone.inr targetArrow).1
              (neg_add_cancel 1)))
          (h := neg_add_cancel 1)
          targetDegree (targetDegree + 1) rfl
            targetDegree (by omega)
    have transitionInr (degree : ℤ) :
        (CochainComplex.mappingCocone.inr arrow).1.v
            degree (degree + 1) rfl ≫
            (CochainMappingCoconeFunctoriality.mappingCoconeMap
              arrow targetArrow sourceTransition targetTransition
                transitionSquare).f (degree + 1) =
          targetTransition.f degree ≫
            (CochainComplex.mappingCocone.inr targetArrow).1.v
              degree (degree + 1) rfl := by
      have generated := Cochain.congr_v
        (mappingCoconeMap_inr_between arrow targetArrow
          sourceTransition targetTransition transitionSquare)
        degree (degree + 1) rfl
      simpa [Cochain.comp_v] using generated
    conv_lhs => rw [← Category.assoc]
    rw [highDesc]
    conv_rhs => rw [← Category.assoc]
    rw [transitionInr targetDegree, Category.assoc, lowDesc]
    simp only [Cochain.neg_v]
    rw [Cochain.comp_v _ _ (neg_add_cancel 1)
        targetDegree (targetDegree + (-1)) targetDegree
          rfl (by omega),
      Cochain.comp_v _ _ (neg_add_cancel 1)
        targetDegree (targetDegree + (-1)) targetDegree
          rfl (by omega)]
    have generated := Cochain.congr_v targetHomotopyTwoCell
      targetDegree (targetDegree + (-1)) rfl
    have generatedComponent :
        (Cochain.ofHomotopy targetHomotopy).v
            targetDegree (targetDegree + (-1)) rfl ≫
            targetTransition.f (targetDegree + (-1)) =
          targetTransition.f targetDegree ≫
            (Cochain.ofHomotopy targetHomotopy').v
              targetDegree (targetDegree + (-1)) rfl := by
      simpa only [Cochain.ofHomotopy, Cochain.mk_v,
        Homotopy.compRight_hom, Homotopy.compLeft_hom] using generated
    have generatedRouted := congrArg
      (fun map ↦ map ≫
        (CochainComplex.mappingCocone.inr targetArrow).1.v
          (targetDegree + (-1)) targetDegree (by omega))
      generatedComponent
    simp only [Category.assoc] at generatedRouted
    have transitionPrevious :
        (CochainComplex.mappingCocone.inr arrow).1.v
              (targetDegree + (-1)) targetDegree (by omega) ≫
            (CochainMappingCoconeFunctoriality.mappingCoconeMap
              arrow targetArrow sourceTransition targetTransition
                transitionSquare).f targetDegree =
          targetTransition.f (targetDegree + (-1)) ≫
            (CochainComplex.mappingCocone.inr targetArrow).1.v
              (targetDegree + (-1)) targetDegree (by omega) := by
      have generated := Cochain.congr_v
        (mappingCoconeMap_inr_between arrow targetArrow
          sourceTransition targetTransition transitionSquare)
        (targetDegree + (-1)) targetDegree (by omega)
      simpa [Cochain.comp_v] using generated
    have transitionRouted := congrArg
      (fun map ↦
        (Cochain.ofHomotopy targetHomotopy).v
          targetDegree (targetDegree + (-1)) rfl ≫ map)
      transitionPrevious
    have positive := transitionRouted.trans generatedRouted
    have negated := congrArg Neg.neg positive
    simpa [Category.assoc] using negated

end MappingCoconeHomotopyDescent

end

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
