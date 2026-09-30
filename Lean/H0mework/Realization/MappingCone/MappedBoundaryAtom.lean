import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Ring-polymorphic Int-index mapped-boundary atoms

For an `Int`-indexed cochain map `φ : K ⟶ L`, an actual degree-one cycle
`z` whose image is the boundary of `q : L.X 0` canonically generates a map
from the scalar single complex into `Fib(φ)`.  This is the direct Int-index
version of the older integral/Nat-extension construction and works over any
commutative coefficient ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace CochainMappingCoconeMappedBoundaryAtomOver

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex.HomComplex

noncomputable section

universe u

variable {R : Type u} [CommRing R]

abbrev ScalarUnit : ModuleCat R := ModuleCat.of R R

abbrev ScalarSingleOne : CochainComplex (ModuleCat R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat R) 1).obj ScalarUnit

noncomputable def elementHom {M : ModuleCat R} (x : M) :
    ScalarUnit ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp] theorem elementHom_one {M : ModuleCat R} (x : M) :
    (elementHom x).hom 1 = x := by
  simp [elementHom, LinearMap.toSpanSingleton_apply]

@[simp] theorem elementHom_comp
    {M N : ModuleCat R} (x : M) (f : M ⟶ N) :
    elementHom x ≫ f = elementHom (f.hom x) := by
  ext
  simp [elementHom, LinearMap.toSpanSingleton_apply]

@[simp] theorem elementHom_neg {M : ModuleCat R} (x : M) :
    elementHom (-x) = -elementHom x := by
  ext
  simp [elementHom, LinearMap.toSpanSingleton_apply]

@[simp] theorem elementHom_zero (M : ModuleCat R) :
    elementHom (0 : M) = 0 := by
  ext
  simp [elementHom]

variable {K L : CochainComplex (ModuleCat R) ℤ}

noncomputable def cycleGenerator (z : K.cycles 1) :
    ScalarUnit ⟶ K.X 1 :=
  elementHom z ≫ K.iCycles 1

noncomputable def boundaryGenerator (q : L.X 0) :
    ScalarUnit ⟶ L.X 0 :=
  elementHom q

noncomputable def cycleMorphism (z : K.cycles 1) :
    ScalarSingleOne ⟶ K :=
  (Cocycle.fromSingleMk
    (cycleGenerator z) (by norm_num) 2 (by norm_num) (by
      unfold cycleGenerator
      rw [Category.assoc, K.iCycles_d 1 2, comp_zero])).homOf

noncomputable def negativeBoundaryCochain (q : L.X 0) :
    Cochain ScalarSingleOne L (-1) :=
  Cochain.fromSingleMk (-boundaryGenerator q) (by norm_num)

theorem cycleGenerator_mapsToBoundary
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    cycleGenerator z ≫ phi.f 1 =
      boundaryGenerator q ≫ L.d 0 1 := by
  change (elementHom z ≫ K.iCycles 1) ≫ phi.f 1 =
    elementHom q ≫ L.d 0 1
  calc
    (elementHom z ≫ K.iCycles 1) ≫ phi.f 1 =
        elementHom z ≫ (cyclesMap phi 1 ≫ L.iCycles 1) := by
      rw [Category.assoc, cyclesMap_i]
    _ = elementHom
        ((L.iCycles 1).hom ((cyclesMap phi 1).hom z)) := by
      rw [← Category.assoc, elementHom_comp, elementHom_comp]
    _ = elementHom ((L.d 0 1).hom q) := by rw [mapped]
    _ = elementHom q ≫ L.d 0 1 := by rw [elementHom_comp]

theorem negativeBoundaryCompatibility
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    δ (-1) 0 (negativeBoundaryCochain q) +
        Cochain.ofHom (cycleMorphism z ≫ phi) = 0 := by
  have generated := cycleGenerator_mapsToBoundary phi z q mapped
  have alphaCochain :
      Cochain.ofHom (cycleMorphism z) =
        Cochain.fromSingleMk (cycleGenerator z) (by norm_num) := by
    unfold cycleMorphism
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  rw [Cochain.ofHom_comp, alphaCochain]
  rw [← Cochain.fromSingleMk_postcomp]
  unfold negativeBoundaryCochain
  rw [Cochain.δ_fromSingleMk]
  rw [← Cochain.fromSingleMk_add]
  have generatorSum :
      (-boundaryGenerator q) ≫ L.d 0 1 +
          cycleGenerator z ≫ phi.f 1 = 0 := by
    rw [Preadditive.neg_comp, generated, neg_add_cancel]
  rw [generatorSum]
  exact Cochain.fromSingleMk_zero ScalarUnit L 1 1 0 (by norm_num)

/-- Direct mapped-boundary atom over the supplied coefficient ring. -/
noncomputable def mappedBoundaryAtom
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    ScalarSingleOne ⟶ CochainComplex.mappingCocone phi :=
  CochainComplex.mappingCocone.lift phi
    (cycleMorphism z) (negativeBoundaryCochain q)
      (negativeBoundaryCompatibility phi z q mapped)

@[reassoc (attr := simp)] theorem mappedBoundaryAtom_fst
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    mappedBoundaryAtom phi z q mapped ≫
        CochainComplex.mappingCocone.fst phi =
      cycleMorphism z :=
  CochainComplex.mappingCocone.lift_fst phi
    (cycleMorphism z) (negativeBoundaryCochain q)
      (negativeBoundaryCompatibility phi z q mapped)

@[reassoc] theorem mappedBoundaryAtom_snd
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    (mappedBoundaryAtom phi z q mapped).f 1 ≫
        (CochainComplex.mappingCocone.snd phi).v 1 0 (by omega) =
      -boundaryGenerator q :=
  CochainComplex.mappingCocone.lift_f_snd_v phi
    (cycleMorphism z) (negativeBoundaryCochain q)
      (negativeBoundaryCompatibility phi z q mapped) 1 0 (by omega)

/-- First-class actual point for consumers that must retain the exact cycle,
boundary, and mapped-boundary incidence together. -/
structure MappedBoundaryPointAt (phi : K ⟶ L) where
  cycle : K.cycles 1
  boundary : L.X 0
  mapped : (L.d 0 1).hom boundary =
    (L.iCycles 1).hom ((cyclesMap phi 1).hom cycle)

namespace MappedBoundaryPointAt

variable {phi : K ⟶ L}

noncomputable def ofPoint (point : MappedBoundaryPointAt phi) :
    ScalarSingleOne ⟶ CochainComplex.mappingCocone phi :=
  mappedBoundaryAtom phi point.cycle point.boundary point.mapped

@[reassoc (attr := simp)] theorem ofPoint_fst
    (point : MappedBoundaryPointAt phi) :
    point.ofPoint ≫ CochainComplex.mappingCocone.fst phi =
      cycleMorphism point.cycle :=
  mappedBoundaryAtom_fst phi point.cycle point.boundary point.mapped

@[reassoc] theorem ofPoint_snd (point : MappedBoundaryPointAt phi) :
    point.ofPoint.f 1 ≫
        (CochainComplex.mappingCocone.snd phi).v 1 0 (by omega) =
      -boundaryGenerator point.boundary :=
  mappedBoundaryAtom_snd phi point.cycle point.boundary point.mapped

end MappedBoundaryPointAt

end
end CochainMappingCoconeMappedBoundaryAtomOver
end SaturationMonoid
