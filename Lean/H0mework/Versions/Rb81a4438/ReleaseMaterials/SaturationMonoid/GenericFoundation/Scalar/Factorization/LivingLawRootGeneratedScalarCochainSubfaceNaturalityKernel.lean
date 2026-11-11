import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Factorization.LivingLawRootGeneratedScalarCochainSubfaceFactorizationKernel

/-!
# Naturality of cochain subface residuals

Every commuting source/subface square transports the canonical range
residual degreewise.  The transport preserves identity and composition on
the complete quotient carrier, not merely on chosen representatives.
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
variable {Source Face Ambient Source' Face' Ambient' :
  HomologicalComplex (ModuleCat.{m} R) shape}

def degreeResidualTransport
    (subface : Face ⟶ Ambient) (subface' : Face' ⟶ Ambient')
    (faceMap : Face ⟶ Face') (ambientMap : Ambient ⟶ Ambient')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (degree : Index) :
    DegreeResidualCarrier subface degree →ₗ[R]
      DegreeResidualCarrier subface' degree :=
  SourceGeneratedSubfaceFactorization.residualTransport
    (degreeSubfaceMap subface degree)
    (degreeSubfaceMap subface' degree)
    (faceMap.f degree).hom
    (ambientMap.f degree).hom
    (by
      apply LinearMap.ext
      intro value
      exact congrArg
        (fun map : Face.X degree ⟶ Ambient'.X degree => map.hom value)
        (congrArg (fun map : Face ⟶ Ambient' => map.f degree)
          subfaceSquare))

theorem degreeResidualMap_naturality
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (source' : Source' ⟶ Ambient') (subface' : Face' ⟶ Ambient')
    (sourceMap : Source ⟶ Source') (faceMap : Face ⟶ Face')
    (ambientMap : Ambient ⟶ Ambient')
    (sourceSquare : source ≫ ambientMap = sourceMap ≫ source')
    (subfaceSquare : subface ≫ ambientMap = faceMap ≫ subface')
    (degree : Index) :
    (degreeResidualTransport subface subface' faceMap ambientMap
        subfaceSquare degree).comp
        (degreeResidualMap source subface degree) =
      (degreeResidualMap source' subface' degree).comp
        (sourceMap.f degree).hom := by
  apply SourceGeneratedSubfaceFactorization.residualMap_naturality
  apply LinearMap.ext
  intro value
  exact congrArg
    (fun map : Source.X degree ⟶ Ambient'.X degree => map.hom value)
    (congrArg (fun map : Source ⟶ Ambient' => map.f degree) sourceSquare)

theorem degreeResidualTransport_id
    (subface : Face ⟶ Ambient) (degree : Index) :
    degreeResidualTransport subface subface (𝟙 Face) (𝟙 Ambient)
        (by simp) degree =
      LinearMap.id := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (degreeSubfaceMap subface degree)) quotientValue
  rfl

variable {Face'' Ambient'' :
  HomologicalComplex (ModuleCat.{m} R) shape}

theorem degreeResidualTransport_comp
    (subface : Face ⟶ Ambient)
    (subface' : Face' ⟶ Ambient')
    (subface'' : Face'' ⟶ Ambient'')
    (faceMap₁ : Face ⟶ Face') (faceMap₂ : Face' ⟶ Face'')
    (ambientMap₁ : Ambient ⟶ Ambient')
    (ambientMap₂ : Ambient' ⟶ Ambient'')
    (square₁ : subface ≫ ambientMap₁ = faceMap₁ ≫ subface')
    (square₂ : subface' ≫ ambientMap₂ = faceMap₂ ≫ subface'')
    (square₁₂ : subface ≫ (ambientMap₁ ≫ ambientMap₂) =
      (faceMap₁ ≫ faceMap₂) ≫ subface'')
    (degree : Index) :
    degreeResidualTransport subface subface''
        (faceMap₁ ≫ faceMap₂) (ambientMap₁ ≫ ambientMap₂)
        square₁₂ degree =
      (degreeResidualTransport subface' subface'' faceMap₂ ambientMap₂
        square₂ degree).comp
      (degreeResidualTransport subface subface' faceMap₁ ambientMap₁
        square₁ degree) := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (degreeSubfaceMap subface degree)) quotientValue
  rfl

end
end SourceGeneratedCochainSubfaceFactorization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
