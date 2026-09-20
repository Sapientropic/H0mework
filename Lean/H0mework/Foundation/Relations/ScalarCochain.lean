import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import H0mework.Foundation.Relations.ScalarPresentation

/-!
# Scalar-polymorphic cochain relation presentation

An actual homological complex of `R`-modules generates, degreewise, the
complete addition-and-scalar relation presentation.  Actual differentials
transport both relation families, the presented maps read back as the
original differentials, and `d² = 0` produces the canonical first syzygy.

No basis, finite chart, perfectness, determinant, or coefficient-forgetting
premise enters the face.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ScalarCochainRelation

open CategoryTheory
open ScalarRelationPresentation

noncomputable section

universe r m u

variable {R : Type r} [CommRing R]
variable {Index : Type*} {shape : ComplexShape Index}

structure RootFace
    {Root : Type u}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (complexAt : Root →
      HomologicalComplex (ModuleCat.{m} R) shape) where
  private mk ::

namespace RootFace

variable {Root : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {complexAt : Root →
  HomologicalComplex (ModuleCat.{m} R) shape}

def generate : RootFace rootOccurrence complexAt :=
  ⟨⟩

def root (_face : RootFace rootOccurrence complexAt) :=
  rootOccurrence

def complexOccurrence (_face : RootFace rootOccurrence complexAt) :
    RootedAccountedUnfolding
      (HomologicalComplex (ModuleCat.{m} R) shape) :=
  rootOccurrence.map complexAt

def complex (_face : RootFace rootOccurrence complexAt) :=
  complexAt rootOccurrence.root

theorem complexOccurrence_is_root_map
    (face : RootFace rootOccurrence complexAt) :
    face.complexOccurrence = rootOccurrence.map complexAt :=
  rfl

def termPresentation
    (face : RootFace rootOccurrence complexAt)
    (degree : Index) :
    ScalarRelationPresentation.RootFace
      (R := R) (G := face.complex.X degree) face.root :=
  ScalarRelationPresentation.RootFace.generate
    (R := R) (G := face.complex.X degree) face.root

def differential
    (face : RootFace rootOccurrence complexAt)
    (source target : Index) :
    face.complex.X source →ₗ[R] face.complex.X target :=
  (face.complex.d source target).hom

def differentialGeneratorMap
    (face : RootFace rootOccurrence complexAt)
    (source target : Index) :=
  ScalarRelationPresentation.generatorMap
    (face.differential source target)

def differentialRelationMap
    (face : RootFace rootOccurrence complexAt)
    (source target : Index) :=
  ScalarRelationPresentation.relationGeneratorMap
    (face.differential source target)

def differentialPresentedMap
    (face : RootFace rootOccurrence complexAt)
    (source target : Index) :=
  ScalarRelationPresentation.presentedMap
    (face.differential source target)

def differentialSquareRelationLift
    (face : RootFace rootOccurrence complexAt)
    (first last : Index) :=
  ScalarRelationPresentation.zeroRelationLift (R := R)
    (face.complex.X first) (face.complex.X last)

theorem differential_relation_naturality
    (face : RootFace rootOccurrence complexAt)
    (source target : Index) :
    (face.differentialGeneratorMap source target).comp
        (ScalarRelationPresentation.relationMap
          (R := R) (face.complex.X source)) =
      (ScalarRelationPresentation.relationMap
        (R := R) (face.complex.X target)).comp
        (face.differentialRelationMap source target) :=
  ScalarRelationPresentation.relationMap_naturality
    (face.differential source target)

theorem differential_presentedMap_commutes
    (face : RootFace rootOccurrence complexAt)
    (source target : Index)
    (value : ScalarRelationPresentation.PresentedCarrier R
      (face.complex.X source)) :
    ScalarRelationPresentation.presentedEquiv
        (R := R) (face.complex.X target)
        (face.differentialPresentedMap source target value) =
      face.differential source target
        (ScalarRelationPresentation.presentedEquiv
          (R := R) (face.complex.X source) value) :=
  ScalarRelationPresentation.presentedMap_commutes
    (face.differential source target) value

theorem differential_presentedMap_comp_zero
    (face : RootFace rootOccurrence complexAt)
    (first middle last : Index)
    (value : ScalarRelationPresentation.PresentedCarrier R
      (face.complex.X first)) :
    ScalarRelationPresentation.presentedEquiv
        (R := R) (face.complex.X last)
        (face.differentialPresentedMap middle last
          (face.differentialPresentedMap first middle value)) = 0 := by
  rw [face.differential_presentedMap_commutes,
    face.differential_presentedMap_commutes]
  exact ConcreteCategory.congr_hom
    (face.complex.d_comp_d first middle last)
    (ScalarRelationPresentation.presentedEquiv
      (R := R) (face.complex.X first) value)

theorem differentialGeneratorMap_comp_factorizes_through_relation
    (face : RootFace rootOccurrence complexAt)
    (first middle last : Index) :
    (face.differentialGeneratorMap middle last).comp
        (face.differentialGeneratorMap first middle) =
      (ScalarRelationPresentation.relationMap
        (R := R) (face.complex.X last)).comp
        (face.differentialSquareRelationLift first last) := by
  apply ScalarRelationPresentation.generatorMap_comp_factorizes_through_zeroRelation
  ext value
  exact ConcreteCategory.congr_hom
    (face.complex.d_comp_d first middle last) value

theorem preserves_exact_root
    (face : RootFace rootOccurrence complexAt) :
    face.root = rootOccurrence :=
  rfl

end RootFace

end
end ScalarCochainRelation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
