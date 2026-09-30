import H0mework.Foundation.Relations.ScalarCochain

/-!
# Maps of scalar cochain relation presentations

An actual chain map on one exact root transports the complete
addition-and-scalar presentations degreewise.  The generated cokernel map is
the actual `R`-linear degree map, and its differential square remains the
source chain-map square.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ScalarCochainRelationMap

open CategoryTheory
open ScalarRelationPresentation
open ScalarCochainRelation

noncomputable section

universe r m u

variable {R : Type r} [CommRing R]
variable {Index : Type*} {shape : ComplexShape Index}
variable {Root : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceComplexAt targetComplexAt : Root →
  HomologicalComplex (ModuleCat.{m} R) shape}

structure RootMap
    (sourceFace : ScalarCochainRelation.RootFace
      rootOccurrence sourceComplexAt)
    (targetFace : ScalarCochainRelation.RootFace
      rootOccurrence targetComplexAt)
    (mapAt : (root : Root) →
      sourceComplexAt root ⟶ targetComplexAt root) where
  private mk ::

namespace RootMap

variable {sourceFace : ScalarCochainRelation.RootFace
  rootOccurrence sourceComplexAt}
variable {targetFace : ScalarCochainRelation.RootFace
  rootOccurrence targetComplexAt}
variable {mapAt : (root : Root) →
  sourceComplexAt root ⟶ targetComplexAt root}

def generate : RootMap sourceFace targetFace mapAt :=
  ⟨⟩

def actualMap (_face : RootMap sourceFace targetFace mapAt) :=
  mapAt rootOccurrence.root

abbrev MapPayload := Σ root : Root,
  sourceComplexAt root ⟶ targetComplexAt root

def mapOccurrence (_face : RootMap sourceFace targetFace mapAt) :
    RootedAccountedUnfolding
      (MapPayload (sourceComplexAt := sourceComplexAt)
        (targetComplexAt := targetComplexAt)) :=
  rootOccurrence.map fun root => ⟨root, mapAt root⟩

theorem mapOccurrence_is_root_map
    (face : RootMap sourceFace targetFace mapAt) :
    face.mapOccurrence =
      rootOccurrence.map (fun root => ⟨root, mapAt root⟩) :=
  rfl

def degreeMap
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index) :
    sourceFace.complex.X degree →ₗ[R] targetFace.complex.X degree :=
  (face.actualMap.f degree).hom

def degreeGeneratorMap
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index) :=
  ScalarRelationPresentation.generatorMap (face.degreeMap degree)

def degreeRelationMap
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index) :=
  ScalarRelationPresentation.relationGeneratorMap (face.degreeMap degree)

def degreePresentedMap
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index) :=
  ScalarRelationPresentation.presentedMap (face.degreeMap degree)

theorem degree_relation_naturality
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index) :
    (face.degreeGeneratorMap degree).comp
        (ScalarRelationPresentation.relationMap
          (R := R) (sourceFace.complex.X degree)) =
      (ScalarRelationPresentation.relationMap
        (R := R) (targetFace.complex.X degree)).comp
        (face.degreeRelationMap degree) :=
  ScalarRelationPresentation.relationMap_naturality
    (face.degreeMap degree)

theorem degree_presentedMap_commutes
    (face : RootMap sourceFace targetFace mapAt)
    (degree : Index)
    (value : ScalarRelationPresentation.PresentedCarrier R
      (sourceFace.complex.X degree)) :
    ScalarRelationPresentation.presentedEquiv
        (R := R) (targetFace.complex.X degree)
        (face.degreePresentedMap degree value) =
      face.degreeMap degree
        (ScalarRelationPresentation.presentedEquiv
          (R := R) (sourceFace.complex.X degree) value) :=
  ScalarRelationPresentation.presentedMap_commutes
    (face.degreeMap degree) value

theorem actualMap_comm
    (face : RootMap sourceFace targetFace mapAt)
    (source target : Index) :
    face.actualMap.f source ≫ targetFace.complex.d source target =
      sourceFace.complex.d source target ≫ face.actualMap.f target :=
  face.actualMap.comm source target

theorem preserves_exact_root
    (_face : RootMap sourceFace targetFace mapAt) :
    sourceFace.root = targetFace.root :=
  rfl

end RootMap

end
end ScalarCochainRelationMap
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
