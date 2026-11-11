import H0mework.Foundation.Relations.Factorization.LivingLawRootGeneratedScalarSubfaceFactorizationKernel
import H0mework.Foundation.Relations.ScalarCochainMap

/-!
# Source-generated cochain subface factorization

The scalar range/cokernel classifier is lifted degreewise to arbitrary
homological-complex shapes.  For an actual degreewise-injective dependent
face, vanishing of every canonical range residual generates the unique chain
map factorization.  Otherwise the disposition retains an explicit degree and
an actual source coordinate outside the dependent face.

The chain law of the generated lift is derived from the two existing chain
squares and degreewise injectivity; it is not supplied by a caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCochainSubfaceFactorization

open CategoryTheory
open SourceGeneratedSubfaceFactorization

noncomputable section

universe r m i

variable {R : Type r} [CommRing R]
variable {Index : Type i} {shape : ComplexShape Index}
variable {Source Face Ambient :
  HomologicalComplex (ModuleCat.{m} R) shape}

def degreeSourceMap (source : Source ⟶ Ambient) (degree : Index) :
    Source.X degree →ₗ[R] Ambient.X degree :=
  (source.f degree).hom

def degreeSubfaceMap (subface : Face ⟶ Ambient) (degree : Index) :
    Face.X degree →ₗ[R] Ambient.X degree :=
  (subface.f degree).hom

abbrev DegreeResidualCarrier
    (subface : Face ⟶ Ambient) (degree : Index) :=
  ResidualCarrier (degreeSubfaceMap subface degree)

def degreeResidualMap
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (degree : Index) :
    Source.X degree →ₗ[R] DegreeResidualCarrier subface degree :=
  residualMap (degreeSourceMap source degree) (degreeSubfaceMap subface degree)

structure DegreewiseInjective (subface : Face ⟶ Ambient) : Prop where
  injective : ∀ degree, Function.Injective (degreeSubfaceMap subface degree)

abbrev DegreeResidualZero
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) :=
  ∀ degree, degreeResidualMap source subface degree = 0

def liftDegree
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (residualZero : DegreeResidualZero source subface)
    (degree : Index) :
    Source.X degree →ₗ[R] Face.X degree :=
  canonicalLift
    (degreeSourceMap source degree)
    (degreeSubfaceMap subface degree)
    (injective.injective degree)
    (residualZero degree)

theorem liftDegree_commutes
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (residualZero : DegreeResidualZero source subface)
    (degree : Index) :
    (degreeSubfaceMap subface degree).comp
        (liftDegree source subface injective residualZero degree) =
      degreeSourceMap source degree :=
  canonicalLift_commutes
    (degreeSourceMap source degree)
    (degreeSubfaceMap subface degree)
    (injective.injective degree)
    (residualZero degree)

def cochainLift
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (residualZero : DegreeResidualZero source subface) :
    Source ⟶ Face where
  f degree := ModuleCat.ofHom
    (liftDegree source subface injective residualZero degree)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro value
    apply injective.injective j
    change
      (subface.f j).hom
          ((Face.d i j).hom
            (liftDegree source subface injective residualZero i value)) =
        (subface.f j).hom
          (liftDegree source subface injective residualZero j
            ((Source.d i j).hom value))
    have subfaceCommAt := congrArg
      (fun map : Face.X i ⟶ Ambient.X j =>
        map.hom (liftDegree source subface injective residualZero i value))
      (subface.comm i j)
    have sourceCommAt := congrArg
      (fun map : Source.X i ⟶ Ambient.X j => map.hom value)
      (source.comm i j)
    have liftAtI := LinearMap.congr_fun
      (liftDegree_commutes source subface injective residualZero i) value
    have liftAtJ := LinearMap.congr_fun
      (liftDegree_commutes source subface injective residualZero j)
      ((Source.d i j).hom value)
    change (subface.f i).hom
        (liftDegree source subface injective residualZero i value) =
      (source.f i).hom value at liftAtI
    change (subface.f j).hom
        (liftDegree source subface injective residualZero j
          ((Source.d i j).hom value)) =
      (source.f j).hom ((Source.d i j).hom value) at liftAtJ
    calc
      (subface.f j).hom
          ((Face.d i j).hom
            (liftDegree source subface injective residualZero i value)) =
          (Ambient.d i j).hom
            ((subface.f i).hom
              (liftDegree source subface injective residualZero i value)) := by
            exact subfaceCommAt.symm
      _ = (Ambient.d i j).hom ((source.f i).hom value) := by
            rw [liftAtI]
      _ = (source.f j).hom ((Source.d i j).hom value) := by
            exact sourceCommAt
      _ = (subface.f j).hom
          (liftDegree source subface injective residualZero j
            ((Source.d i j).hom value)) := by
            exact liftAtJ.symm

theorem cochainLift_commutes
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (residualZero : DegreeResidualZero source subface) :
    cochainLift source subface injective residualZero ≫ subface = source := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply ModuleCat.hom_ext
  exact liftDegree_commutes source subface injective residualZero degree

structure Factorization
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) where
  lift : Source ⟶ Face
  commutes : lift ≫ subface = source

theorem factorization_unique
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (left right : Factorization source subface) :
    left.lift = right.lift := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  apply injective.injective degree
  have leftAt := congrArg
    (fun map : Source.X degree ⟶ Ambient.X degree => map.hom value)
    (congrArg (fun map : Source ⟶ Ambient => map.f degree) left.commutes)
  have rightAt := congrArg
    (fun map : Source.X degree ⟶ Ambient.X degree => map.hom value)
    (congrArg (fun map : Source ⟶ Ambient => map.f degree) right.commutes)
  exact leftAt.trans rightAt.symm

theorem factorization_nonempty_iff_degreeResidualZero
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface) :
    Nonempty (Factorization source subface) ↔
      DegreeResidualZero source subface := by
  constructor
  · rintro ⟨factorization⟩ degree
    apply (SourceGeneratedSubfaceFactorization.factorization_nonempty_iff_residualMap_eq_zero
        (degreeSourceMap source degree)
        (degreeSubfaceMap subface degree)
        (injective.injective degree)).mp
    refine ⟨⟨(factorization.lift.f degree).hom, ?_⟩⟩
    have degreeEquality := congrArg
      (fun map : Source ⟶ Ambient => map.f degree)
      factorization.commutes
    apply LinearMap.ext
    intro value
    exact congrArg (fun map : Source.X degree ⟶ Ambient.X degree =>
      map.hom value) degreeEquality
  · intro residualZero
    exact ⟨⟨cochainLift source subface injective residualZero,
      cochainLift_commutes source subface injective residualZero⟩⟩

structure DegreeResidualCoordinate
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) where
  degree : Index
  coordinate : SourceGeneratedSubfaceFactorization.ResidualCoordinate
    (degreeSourceMap source degree) (degreeSubfaceMap subface degree)

inductive Disposition
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) :
    Type (max (max r m) i + 2) where
  | factors (factorization : Factorization source subface)
  | residual (coordinate : DegreeResidualCoordinate source subface)

noncomputable def settle
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface) :
    Disposition source subface := by
  classical
  by_cases residualZero : DegreeResidualZero source subface
  · exact .factors
      ⟨cochainLift source subface injective residualZero,
        cochainLift_commutes source subface injective residualZero⟩
  · have existsDegree : ∃ degree,
        degreeResidualMap source subface degree ≠ 0 := by
      by_contra noDegree
      apply residualZero
      intro degree
      by_contra degree_ne
      exact noDegree ⟨degree, degree_ne⟩
    let degree := Classical.choose existsDegree
    have degree_ne : degreeResidualMap source subface degree ≠ 0 :=
      Classical.choose_spec existsDegree
    exact Disposition.residual ⟨degree,
      ((SourceGeneratedSubfaceFactorization.residualMap_ne_zero_iff_exists_coordinate
          (degreeSourceMap source degree)
          (degreeSubfaceMap subface degree)).mp degree_ne).some⟩

theorem settle_total
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface) :
    Nonempty (Disposition source subface) :=
  ⟨settle source subface injective⟩

end
end SourceGeneratedCochainSubfaceFactorization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
