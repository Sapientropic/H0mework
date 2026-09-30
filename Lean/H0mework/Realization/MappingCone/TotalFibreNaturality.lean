import H0mework.Realization.MappingCone.TotalFibreSymmetry

/-!
# Naturality of total-fibre transposition

A morphism between two homotopy-commutative cochain squares consists of four
actual edge maps, four strict face equations, and the actual two-cell
naturality law.  Mapping-cocone functoriality generates both iterated-fibre
transitions, and canonical total-fibre transposition commutes with them.

No comparison isomorphism, quasi-isomorphism, exactness, or vanishing receipt
enters the mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainMappingCoconeTotalFiberNaturality

open CategoryTheory
open CochainComplex.HomComplex
open CochainMappingCoconeDegreewiseKernel
open CochainMappingCoconeFunctoriality
open CochainMappingCoconeHomotopyFunctoriality
open CochainMappingCoconeTotalFiberSymmetry

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasBinaryBiproducts C]

/-- One actual cube between two homotopy-commutative cochain squares. -/
structure HomotopyCommutativeCochainSquareMorphismAt
    (high low : HomotopyCommutativeCochainSquareAt C) where
  upperLeft : high.upperLeft ⟶ low.upperLeft
  upperRight : high.upperRight ⟶ low.upperRight
  lowerLeft : high.lowerLeft ⟶ low.lowerLeft
  lowerRight : high.lowerRight ⟶ low.lowerRight
  upperSquare : upperLeft ≫ low.horizontalSource =
    high.horizontalSource ≫ upperRight
  lowerSquare : lowerLeft ≫ low.horizontalTarget =
    high.horizontalTarget ≫ lowerRight
  leftSquare : upperLeft ≫ low.verticalLeft =
    high.verticalLeft ≫ lowerLeft
  rightSquare : upperRight ≫ low.verticalRight =
    high.verticalRight ≫ lowerRight
  twoCell : Cochain.ofHomotopy (high.square.compRight lowerRight) =
    Cochain.ofHomotopy (low.square.compLeft upperLeft)

namespace HomotopyCommutativeCochainSquareMorphismAt

variable {high low : HomotopyCommutativeCochainSquareAt C}
variable (cube : HomotopyCommutativeCochainSquareMorphismAt high low)

noncomputable def upperTransition :
    CochainComplex.mappingCocone high.horizontalSource ⟶
      CochainComplex.mappingCocone low.horizontalSource :=
  mappingCoconeMap high.horizontalSource low.horizontalSource
    cube.upperLeft cube.upperRight cube.upperSquare

noncomputable def lowerTransition :
    CochainComplex.mappingCocone high.horizontalTarget ⟶
      CochainComplex.mappingCocone low.horizontalTarget :=
  mappingCoconeMap high.horizontalTarget low.horizontalTarget
    cube.lowerLeft cube.lowerRight cube.lowerSquare

theorem horizontalMapSquare :
    cube.upperTransition ≫
        horizontalMap low.horizontalSource low.horizontalTarget
          low.verticalLeft low.verticalRight low.square =
      horizontalMap high.horizontalSource high.horizontalTarget
          high.verticalLeft high.verticalRight high.square ≫
        cube.lowerTransition :=
  mappingCoconeMap_cube
    high.horizontalSource low.horizontalSource
    high.horizontalTarget low.horizontalTarget
    cube.upperLeft cube.upperRight cube.upperSquare
    cube.lowerLeft cube.lowerRight cube.lowerSquare
    high.verticalLeft high.verticalRight high.square
    low.verticalLeft low.verticalRight low.square
    cube.leftSquare cube.rightSquare cube.twoCell

noncomputable def horizontalTotalTransition :
    high.horizontalTotal ⟶ low.horizontalTotal :=
  mappingCoconeMap
    (horizontalMap high.horizontalSource high.horizontalTarget
      high.verticalLeft high.verticalRight high.square)
    (horizontalMap low.horizontalSource low.horizontalTarget
      low.verticalLeft low.verticalRight low.square)
    cube.upperTransition cube.lowerTransition cube.horizontalMapSquare

noncomputable def leftTransition :
    CochainComplex.mappingCocone high.verticalLeft ⟶
      CochainComplex.mappingCocone low.verticalLeft :=
  mappingCoconeMap high.verticalLeft low.verticalLeft
    cube.upperLeft cube.lowerLeft cube.leftSquare

noncomputable def rightTransition :
    CochainComplex.mappingCocone high.verticalRight ⟶
      CochainComplex.mappingCocone low.verticalRight :=
  mappingCoconeMap high.verticalRight low.verticalRight
    cube.upperRight cube.lowerRight cube.rightSquare

theorem symmTwoCell :
    Cochain.ofHomotopy (high.square.symm.compRight cube.lowerRight) =
      Cochain.ofHomotopy (low.square.symm.compLeft cube.upperLeft) := by
  ext sourceDegree targetDegree degree_eq : 1
  have generated := Cochain.congr_v cube.twoCell
    sourceDegree targetDegree degree_eq
  simp only [Cochain.ofHomotopy, Cochain.mk_v,
    Homotopy.compRight_hom, Homotopy.compLeft_hom,
    Homotopy.symm_hom, Preadditive.neg_comp,
    Preadditive.comp_neg]
  exact congrArg Neg.neg generated

theorem verticalMapSquare :
    cube.leftTransition ≫
        verticalMap low.horizontalSource low.horizontalTarget
          low.verticalLeft low.verticalRight low.square =
      verticalMap high.horizontalSource high.horizontalTarget
          high.verticalLeft high.verticalRight high.square ≫
        cube.rightTransition :=
  mappingCoconeMap_cube
    high.verticalLeft low.verticalLeft
    high.verticalRight low.verticalRight
    cube.upperLeft cube.lowerLeft cube.leftSquare
    cube.upperRight cube.lowerRight cube.rightSquare
    high.horizontalSource high.horizontalTarget high.square.symm
    low.horizontalSource low.horizontalTarget low.square.symm
    cube.upperSquare cube.lowerSquare cube.symmTwoCell

noncomputable def verticalTotalTransition :
    high.verticalTotal ⟶ low.verticalTotal :=
  mappingCoconeMap
    (verticalMap high.horizontalSource high.horizontalTarget
      high.verticalLeft high.verticalRight high.square)
    (verticalMap low.horizontalSource low.horizontalTarget
      low.verticalLeft low.verticalRight low.square)
    cube.leftTransition cube.rightTransition cube.verticalMapSquare

theorem verticalTotalTransition_fst :
    cube.verticalTotalTransition ≫
        CochainComplex.mappingCocone.fst
          (verticalMap low.horizontalSource low.horizontalTarget
            low.verticalLeft low.verticalRight low.square) =
      CochainComplex.mappingCocone.fst
          (verticalMap high.horizontalSource high.horizontalTarget
            high.verticalLeft high.verticalRight high.square) ≫
        cube.leftTransition := by
  unfold verticalTotalTransition
  exact mappingCoconeMap_fst
    (verticalMap high.horizontalSource high.horizontalTarget
      high.verticalLeft high.verticalRight high.square)
    (verticalMap low.horizontalSource low.horizontalTarget
      low.verticalLeft low.verticalRight low.square)
    cube.leftTransition cube.rightTransition cube.verticalMapSquare

private theorem strictMappingCoconeMap_fst_f
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right)
    (degree : ℤ) :
    (mappingCoconeMap phi phi' left right commutes).f degree ≫
        (CochainComplex.mappingCocone.fst phi').f degree =
      (CochainComplex.mappingCocone.fst phi).f degree ≫
        left.f degree := by
  have generated := congrArg (fun morphism => morphism.f degree)
    (mappingCoconeMap_fst phi phi' left right commutes)
  rw [HomologicalComplex.comp_f] at generated
  exact generated

private theorem strictMappingCoconeMap_snd_v
    {K L K' L' : CochainComplex C ℤ}
    (phi : K ⟶ L) (phi' : K' ⟶ L')
    (left : K ⟶ K') (right : L ⟶ L')
    (commutes : left ≫ phi' = phi ≫ right)
    (sourceDegree targetDegree : ℤ)
    (degree_eq : sourceDegree + (-1) = targetDegree) :
    (mappingCoconeMap phi phi' left right commutes).f sourceDegree ≫
        (CochainComplex.mappingCocone.snd phi').v
          sourceDegree targetDegree degree_eq =
      (CochainComplex.mappingCocone.snd phi).v
          sourceDegree targetDegree degree_eq ≫
        right.f targetDegree := by
  have generated := Cochain.congr_v
    (mappingCoconeMap_snd phi phi' left right commutes)
    sourceDegree targetDegree degree_eq
  simpa only [Cochain.zero_cochain_comp_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using generated

@[simp] theorem generatedTotalIso_hom_f
    (actual : HomotopyCommutativeCochainSquareAt C)
    (degree : ℤ) :
    actual.generatedTotalIso.hom.f degree =
      transposeComponent actual.horizontalSource actual.horizontalTarget
        actual.verticalLeft actual.verticalRight actual.square degree :=
  rfl

/-- Canonical total-fibre transposition is strictly natural for every actual
cube of homotopy-commutative cochain squares. -/
theorem generatedTotalIso_naturality :
    cube.horizontalTotalTransition ≫ low.generatedTotalIso.hom =
      high.generatedTotalIso.hom ≫ cube.verticalTotalTransition := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply degree_hom_ext
    (verticalMap low.horizontalSource low.horizontalTarget
      low.verticalLeft low.verticalRight low.square) degree
  · apply degree_hom_ext low.verticalLeft degree
    · simp only [HomologicalComplex.comp_f,
        horizontalTotalTransition, verticalTotalTransition,
        upperTransition, leftTransition, generatedTotalIso_hom_f,
        Category.assoc, transposeComponent_A,
        strictMappingCoconeMap_fst_f]
      rw [← Category.assoc, strictMappingCoconeMap_fst_f]
      rw [Category.assoc, strictMappingCoconeMap_fst_f]
      rw [← Category.assoc, ← transposeComponent_A]
      simp only [Category.assoc]
    · simp only [HomologicalComplex.comp_f,
        horizontalTotalTransition, verticalTotalTransition,
        lowerTransition, leftTransition, generatedTotalIso_hom_f,
        Category.assoc, transposeComponent_C,
        strictMappingCoconeMap_fst_f, strictMappingCoconeMap_snd_v]
      rw [← Category.assoc, strictMappingCoconeMap_snd_v]
      rw [Category.assoc, strictMappingCoconeMap_fst_f]
      rw [← Category.assoc, ← transposeComponent_C]
      simp only [Category.assoc]
  · let previous := degree + (-1)
    apply degree_hom_ext low.verticalRight previous
    · simp only [HomologicalComplex.comp_f,
        horizontalTotalTransition, verticalTotalTransition,
        upperTransition, rightTransition, generatedTotalIso_hom_f,
        Category.assoc, strictMappingCoconeMap_snd_v]
      dsimp only [previous]
      rw [transposeComponent_B]
      rw [← Category.assoc, strictMappingCoconeMap_fst_f]
      rw [Category.assoc, strictMappingCoconeMap_snd_v]
      rw [← Category.assoc, strictMappingCoconeMap_fst_f]
      rw [← Category.assoc, ← transposeComponent_B]
      simp only [Category.assoc]
    · simp only [HomologicalComplex.comp_f,
        horizontalTotalTransition, verticalTotalTransition,
        lowerTransition, rightTransition, generatedTotalIso_hom_f,
        Category.assoc, strictMappingCoconeMap_snd_v]
      dsimp only [previous]
      rw [transposeComponent_D]
      rw [Preadditive.comp_neg]
      rw [← Category.assoc, strictMappingCoconeMap_snd_v]
      rw [Category.assoc, strictMappingCoconeMap_snd_v]
      rw [strictMappingCoconeMap_snd_v]
      have highD := congrArg
        (fun morphism => morphism ≫ cube.lowerRight.f
          (degree + (-1) + (-1)))
        (transposeComponent_D high.horizontalSource high.horizontalTarget
          high.verticalLeft high.verticalRight high.square degree)
      simpa only [Category.assoc, Preadditive.neg_comp] using highD.symm

/-- The inverse total-fibre transposition is strictly natural as a formal
consequence of the generated hom square and the two canonical inverse laws. -/
theorem generatedTotalIso_inv_naturality :
    high.generatedTotalIso.inv ≫ cube.horizontalTotalTransition =
      cube.verticalTotalTransition ≫ low.generatedTotalIso.inv := by
  apply (cancel_mono low.generatedTotalIso.hom).mp
  rw [Category.assoc, Category.assoc, generatedTotalIso_naturality]
  simp

end HomotopyCommutativeCochainSquareMorphismAt

end

end CochainMappingCoconeTotalFiberNaturality
end SaturationMonoid
