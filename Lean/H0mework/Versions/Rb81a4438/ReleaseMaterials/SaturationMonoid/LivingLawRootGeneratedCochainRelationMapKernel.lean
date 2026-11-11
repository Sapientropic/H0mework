import H0mework.Foundation.Relations.CochainPresentation

/-!
# Root-generated maps of cochain relation presentations

An actual morphism of integral complexes generates degreewise transports of
the canonical source generators and relations.  The map occurrence already
contains the chain-map square; generic presentation functoriality proves that
each induced cokernel map is exactly its actual degree map.  No matrix,
quasi-isomorphism, perfectness or determinant is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CochainRelationMap

open CategoryTheory
open CochainRelationPresentation
open FiniteAdditiveRelationPresentation

noncomputable section

universe u

variable {Index : Type*} {shape : ComplexShape Index}
variable {Root : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceComplexOccurrence targetComplexOccurrence :
  RootedAccountedUnfolding (HomologicalComplex (ModuleCat.{0} ℤ) shape)}

/-- One actual complex map between two presentations on the same exact root
occurrence. -/
structure RootGeneratedCochainRelationMapAt
    (sourceFace : RootGeneratedCochainRelationPresentationAt
      rootOccurrence sourceComplexOccurrence)
    (targetFace : RootGeneratedCochainRelationPresentationAt
      rootOccurrence targetComplexOccurrence)
    (mapOccurrence : RootedAccountedUnfolding
      (sourceFace.complex ⟶ targetFace.complex)) where
  private mk ::

namespace RootGeneratedCochainRelationMapAt

variable {sourceFace : RootGeneratedCochainRelationPresentationAt
  rootOccurrence sourceComplexOccurrence}
variable {targetFace : RootGeneratedCochainRelationPresentationAt
  rootOccurrence targetComplexOccurrence}
variable {mapOccurrence : RootedAccountedUnfolding
  (sourceFace.complex ⟶ targetFace.complex)}

def generate : RootGeneratedCochainRelationMapAt
    sourceFace targetFace mapOccurrence :=
  ⟨⟩

def actualMap
    (_face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence) :=
  mapOccurrence.root

def degreeAddHom
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index) :
    sourceFace.complex.X degree →+ targetFace.complex.X degree :=
  (face.actualMap.f degree).hom.toAddMonoidHom

def degreeGeneratorMap
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index) :=
  generatorMap (face.degreeAddHom degree)

def degreeRelationMap
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index) :=
  relationGeneratorMap (face.degreeAddHom degree)

def degreePresentedMap
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index) :=
  presentedMap (face.degreeAddHom degree)

theorem degree_relation_naturality
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index) :
    (face.degreeGeneratorMap degree).comp
        (additionRelationMap (sourceFace.complex.X degree)) =
      (additionRelationMap (targetFace.complex.X degree)).comp
        (face.degreeRelationMap degree) :=
  additionRelationMap_naturality (face.degreeAddHom degree)

theorem degree_presentedMap_commutes
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (degree : Index)
    (value : (sourceFace.termPresentation degree).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        (targetFace.termPresentation degree)
        (face.degreePresentedMap degree value) =
      face.degreeAddHom degree
        (finiteAdditiveRelationPresentation_cokernelEquiv _
          (sourceFace.termPresentation degree) value) :=
  presentedMap_commutes (face.degreeAddHom degree) value

/-- The source-owned chain-map square remains intrinsic to the same actual
map occurrence. -/
theorem actualMap_comm
    (face : RootGeneratedCochainRelationMapAt
      sourceFace targetFace mapOccurrence)
    (source target : Index) :
    face.actualMap.f source ≫ targetFace.complex.d source target =
      sourceFace.complex.d source target ≫ face.actualMap.f target :=
  face.actualMap.comm source target

end RootGeneratedCochainRelationMapAt

end


end CochainRelationMap
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
