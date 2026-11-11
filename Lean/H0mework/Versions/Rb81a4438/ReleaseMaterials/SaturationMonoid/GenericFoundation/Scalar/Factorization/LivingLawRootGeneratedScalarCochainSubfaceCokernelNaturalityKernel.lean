import Mathlib.Algebra.Homology.DerivedCategory.Basic
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Factorization.LivingLawRootGeneratedScalarCochainSubfaceCokernelKernel

/-!
# Naturality of source-generated cochain subface cokernels

Strict subface squares generate categorical cokernel maps whose components
are exactly the existing quotient residual transports.  Source squares may
commute strictly, up to chain homotopy, or only after derived localization;
the last case concludes only an equality of `DerivedCategory.Q.map` arrows.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCochainSubfaceCokernel

open CategoryTheory CategoryTheory.Limits
open SourceGeneratedSubfaceFactorization
open SourceGeneratedCochainSubfaceFactorization

noncomputable section

universe r m i

variable {R : Type r} [CommRing R]
variable {Index : Type i} {shape : ComplexShape Index}
variable {Source Face Ambient Source' Face' Ambient' :
  HomologicalComplex (ModuleCat.{m} R) shape}

/-- A strict square of subfaces induces the actual categorical map between
their residual complexes. -/
noncomputable def residualComplexMap
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface') :
    ResidualComplex subface ⟶ ResidualComplex subface' :=
  cokernel.map subface subface' faceMap ambientMap subfaceSquare

theorem categoricalProjection_naturality
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface') :
    cokernel.π subface ≫
        residualComplexMap subface subface' faceMap ambientMap subfaceSquare =
      ambientMap ≫ cokernel.π subface' := by
  simp [residualComplexMap]

theorem categoricalResidual_naturality
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (source' : Source' ⟶ Ambient') (subface' : Face' ⟶ Ambient')
    (sourceMap : Source ⟶ Source') (faceMap : Face ⟶ Face')
    (ambientMap : Ambient ⟶ Ambient')
    (sourceSquare : source ≫ ambientMap = sourceMap ≫ source')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface') :
    categoricalResidual source subface ≫
        residualComplexMap subface subface' faceMap ambientMap subfaceSquare =
      sourceMap ≫ categoricalResidual source' subface' := by
  simp only [categoricalResidual, Category.assoc]
  rw [categoricalProjection_naturality, ← Category.assoc, sourceSquare,
    Category.assoc]

theorem degreeSubfaceSquare
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (degree : Index) :
    (ambientMap.f degree).hom.comp (degreeSubfaceMap subface degree) =
      (degreeSubfaceMap subface' degree).comp (faceMap.f degree).hom := by
  apply LinearMap.ext
  intro value
  have componentSquare := congrArg (fun arrow => arrow.f degree) subfaceSquare
  exact ConcreteCategory.congr_hom componentSquare value

/-- The pre-existing quotient residual transport on the components of a
strict cochain subface square. -/
noncomputable def degreeResidualTransport
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (degree : Index) :
    DegreeResidualCarrier subface degree →ₗ[R]
      DegreeResidualCarrier subface' degree :=
  residualTransport
    (degreeSubfaceMap subface degree)
    (degreeSubfaceMap subface' degree)
    (faceMap.f degree).hom (ambientMap.f degree).hom
    (degreeSubfaceSquare subface subface' faceMap ambientMap
      subfaceSquare degree)

/-- The categorical cokernel map has exactly the old quotient residual
transport as each component. -/
theorem residualComplexMap_component
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (degree : Index) :
    (residualComplexMap subface subface' faceMap ambientMap
        subfaceSquare).f degree ≫
        (degreeResidualIso subface' degree).hom =
      (degreeResidualIso subface degree).hom ≫
        ModuleCat.ofHom
          (degreeResidualTransport subface subface' faceMap ambientMap
            subfaceSquare degree) := by
  apply (cancel_epi ((cokernel.π subface).f degree)).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  have projectionSquare := congrArg (fun arrow => arrow.f degree)
    (categoricalProjection_naturality subface subface' faceMap ambientMap
      subfaceSquare)
  have projectionSquareAt := ConcreteCategory.congr_hom projectionSquare value
  have projectionSquareAt' :
      ((residualComplexMap subface subface' faceMap ambientMap
          subfaceSquare).f degree).hom
          (((cokernel.π subface).f degree).hom value) =
        ((cokernel.π subface').f degree).hom
          ((ambientMap.f degree).hom value) := by
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
      using projectionSquareAt
  have lowProjection := ConcreteCategory.congr_hom
    (categoricalProjection_component subface degree) value
  have lowProjection' :
      ConcreteCategory.hom ((degreeResidualIso subface degree).hom)
          (ConcreteCategory.hom ((cokernel.π subface).f degree) value) =
        ConcreteCategory.hom
          (ModuleCat.ofHom
            (LinearMap.range (degreeSubfaceMap subface degree)).mkQ) value := by
    simpa only [ConcreteCategory.comp_apply] using lowProjection
  have highProjection := ConcreteCategory.congr_hom
    (categoricalProjection_component subface' degree)
      ((ambientMap.f degree).hom value)
  have highProjection' :
      ConcreteCategory.hom ((degreeResidualIso subface' degree).hom)
          (ConcreteCategory.hom ((cokernel.π subface').f degree)
            ((ambientMap.f degree).hom value)) =
        ConcreteCategory.hom
          (ModuleCat.ofHom
            (LinearMap.range (degreeSubfaceMap subface' degree)).mkQ)
          ((ambientMap.f degree).hom value) := by
    simpa only [ConcreteCategory.comp_apply] using highProjection
  change
    ((degreeResidualIso subface' degree).hom)
        (((residualComplexMap subface subface' faceMap ambientMap
          subfaceSquare).f degree)
          (((cokernel.π subface).f degree) value)) =
      (degreeResidualTransport subface subface' faceMap ambientMap
        subfaceSquare degree)
        (((degreeResidualIso subface degree).hom)
          (((cokernel.π subface).f degree) value))
  rw [projectionSquareAt', highProjection', lowProjection']
  exact (residualTransport_mk
    (degreeSubfaceMap subface degree)
    (degreeSubfaceMap subface' degree)
    (faceMap.f degree).hom (ambientMap.f degree).hom
    (degreeSubfaceSquare subface subface' faceMap ambientMap
      subfaceSquare degree) value).symm

/-- A source square commuting up to chain homotopy induces the corresponding
homotopy of categorical residual maps. -/
noncomputable def categoricalResidualHomotopyNaturality
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (source' : Source' ⟶ Ambient') (subface' : Face' ⟶ Ambient')
    (sourceMap : Source ⟶ Source') (faceMap : Face ⟶ Face')
    (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (sourceHomotopy :
      Homotopy (source ≫ ambientMap) (sourceMap ≫ source')) :
    Homotopy
      (categoricalResidual source subface ≫
        residualComplexMap subface subface' faceMap ambientMap subfaceSquare)
      (sourceMap ≫ categoricalResidual source' subface') :=
  (Homotopy.ofEq (by
    simp only [categoricalResidual, Category.assoc]
    rw [categoricalProjection_naturality])).trans
    ((sourceHomotopy.compRight (cokernel.π subface')).trans
      (Homotopy.ofEq (by simp only [categoricalResidual, Category.assoc])))

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {SourceD FaceD AmbientD SourceD' FaceD' AmbientD' :
  CochainComplex (ModuleCat.{m} R) ℤ}

/-- A source square already known after localization generates the residual
square after localization. -/
theorem derivedCategoricalResidual_naturality
    (source : SourceD ⟶ AmbientD) (subface : FaceD ⟶ AmbientD)
    (source' : SourceD' ⟶ AmbientD') (subface' : FaceD' ⟶ AmbientD')
    (sourceMap : SourceD ⟶ SourceD') (faceMap : FaceD ⟶ FaceD')
    (ambientMap : AmbientD ⟶ AmbientD')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (derivedSourceSquare :
      DerivedCategory.Q.map (source ≫ ambientMap) =
        DerivedCategory.Q.map (sourceMap ≫ source')) :
    DerivedCategory.Q.map (categoricalResidual source subface) ≫
        DerivedCategory.Q.map
          (residualComplexMap subface subface' faceMap ambientMap
            subfaceSquare) =
      DerivedCategory.Q.map sourceMap ≫
        DerivedCategory.Q.map (categoricalResidual source' subface') := by
  have postcomposed := congrArg
    (fun arrow => arrow ≫ DerivedCategory.Q.map (cokernel.π subface'))
    derivedSourceSquare
  have projected := congrArg DerivedCategory.Q.map
    (categoricalProjection_naturality subface subface' faceMap ambientMap
      subfaceSquare)
  simp only [Functor.map_comp] at projected
  simp only [categoricalResidual, Functor.map_comp, Category.assoc]
  rw [projected]
  simpa only [Functor.map_comp, Category.assoc] using postcomposed

theorem derivedCategoricalResidual_naturality_of_homotopy
    (source : SourceD ⟶ AmbientD) (subface : FaceD ⟶ AmbientD)
    (source' : SourceD' ⟶ AmbientD') (subface' : FaceD' ⟶ AmbientD')
    (sourceMap : SourceD ⟶ SourceD') (faceMap : FaceD ⟶ FaceD')
    (ambientMap : AmbientD ⟶ AmbientD')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (sourceHomotopy :
      Homotopy (source ≫ ambientMap) (sourceMap ≫ source')) :
    DerivedCategory.Q.map (categoricalResidual source subface) ≫
        DerivedCategory.Q.map
          (residualComplexMap subface subface' faceMap ambientMap
            subfaceSquare) =
      DerivedCategory.Q.map sourceMap ≫
        DerivedCategory.Q.map (categoricalResidual source' subface') :=
  derivedCategoricalResidual_naturality source subface source' subface'
    sourceMap faceMap ambientMap subfaceSquare
    (DerivedCategory.Q_map_eq_of_homotopy
      (C := ModuleCat.{m} R) sourceHomotopy)

theorem qMap_precomp_eq
    {A B C : CochainComplex (ModuleCat.{m} R) ℤ}
    (pre : A ⟶ B) {left right : B ⟶ C}
    (equality : DerivedCategory.Q.map left = DerivedCategory.Q.map right) :
    DerivedCategory.Q.map (pre ≫ left) =
      DerivedCategory.Q.map (pre ≫ right) := by
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, equality]

theorem qMap_postcomp_eq
    {A B C : CochainComplex (ModuleCat.{m} R) ℤ}
    {left right : A ⟶ B} (suffix : B ⟶ C)
    (equality : DerivedCategory.Q.map left = DerivedCategory.Q.map right) :
    DerivedCategory.Q.map (left ≫ suffix) =
      DerivedCategory.Q.map (right ≫ suffix) := by
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, equality]

end Derived
end
end SourceGeneratedCochainSubfaceCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
