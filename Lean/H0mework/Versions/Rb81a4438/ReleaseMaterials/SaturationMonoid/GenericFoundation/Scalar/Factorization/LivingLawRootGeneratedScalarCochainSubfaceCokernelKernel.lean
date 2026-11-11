import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Factorization.LivingLawRootGeneratedScalarCochainSubfaceFactorizationKernel

/-!
# Source-generated cochain subface categorical residual

An actual cochain subface generates its categorical cokernel complex and the
actual source residual chain map.  Evaluation of that cokernel is canonically
the existing degreewise quotient by the linear range.  For a degreewise
injective subface, residual vanishing generates the unique factorization via
the abelian kernel-of-cokernel property.
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
variable {Source Face Ambient :
  HomologicalComplex (ModuleCat.{m} R) shape}

/-- The actual categorical residual complex of a cochain subface. -/
abbrev ResidualComplex (subface : Face ⟶ Ambient) :=
  cokernel subface

/-- The source map followed by the categorical cokernel projection. -/
noncomputable def categoricalResidual
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) :
    Source ⟶ ResidualComplex subface :=
  source ≫ cokernel.π subface

/-- Evaluation of the categorical cokernel is the existing quotient by the
degreewise linear range. -/
noncomputable def degreeResidualIso
    (subface : Face ⟶ Ambient) (degree : Index) :
    (ResidualComplex subface).X degree ≅
      ModuleCat.of R (DegreeResidualCarrier subface degree) :=
  PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat.{m} R) shape degree) subface ≪≫
    ModuleCat.cokernelIsoRangeQuotient
      ((HomologicalComplex.eval (ModuleCat.{m} R) shape degree).map subface)

theorem categoricalProjection_component
    (subface : Face ⟶ Ambient) (degree : Index) :
    (cokernel.π subface).f degree ≫ (degreeResidualIso subface degree).hom =
      ModuleCat.ofHom
        (LinearMap.range (degreeSubfaceMap subface degree)).mkQ := by
  change
    (HomologicalComplex.eval (ModuleCat.{m} R) shape degree).map
          (cokernel.π subface) ≫
        ((PreservesCokernel.iso
            (HomologicalComplex.eval (ModuleCat.{m} R) shape degree)
            subface ≪≫
          ModuleCat.cokernelIsoRangeQuotient
            ((HomologicalComplex.eval (ModuleCat.{m} R) shape degree).map
              subface))).hom =
      ModuleCat.ofHom
        (LinearMap.range
          ((HomologicalComplex.eval (ModuleCat.{m} R) shape degree).map
            subface).hom).mkQ
  rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
  exact ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
    ((HomologicalComplex.eval (ModuleCat.{m} R) shape degree).map subface)

theorem categoricalResidual_component
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (degree : Index) :
    (categoricalResidual source subface).f degree ≫
        (degreeResidualIso subface degree).hom =
      ModuleCat.ofHom (degreeResidualMap source subface degree) := by
  rw [categoricalResidual, HomologicalComplex.comp_f, Category.assoc,
    categoricalProjection_component]
  rfl

theorem categoricalResidual_eq_zero_iff_degreeResidualZero
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient) :
    categoricalResidual source subface = 0 ↔
      DegreeResidualZero source subface := by
  constructor
  · intro residualZero degree
    have componentZero :
        ModuleCat.ofHom (degreeResidualMap source subface degree) = 0 := by
      rw [← categoricalResidual_component source subface degree,
        residualZero, HomologicalComplex.zero_f, zero_comp]
    exact congrArg (fun arrow => arrow.hom) componentZero
  · intro residualZero
    apply HomologicalComplex.hom_ext
    intro degree
    apply (cancel_mono (degreeResidualIso subface degree).hom).1
    rw [categoricalResidual_component, residualZero degree]
    simp

theorem monoOfDegreewiseInjective
    (subface : Face ⟶ Ambient) (injective : DegreewiseInjective subface) :
    Mono subface :=
  HomologicalComplex.mono_of_mono_f subface (fun degree =>
    (ModuleCat.mono_iff_injective (subface.f degree)).mpr
      (injective.injective degree))

/-- Categorical residual vanishing directly generates the factorization via
`Abelian.monoLift`. -/
noncomputable def categoricalFactorizationOfResidualZero
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface)
    (residualZero : categoricalResidual source subface = 0) :
    SourceGeneratedCochainSubfaceFactorization.Factorization
      source subface := by
  letI : Mono subface := monoOfDegreewiseInjective subface injective
  change source ≫ cokernel.π subface = 0 at residualZero
  exact
    { lift := Abelian.monoLift subface source residualZero
      commutes := Abelian.monoLift_comp subface source residualZero }

theorem factorization_nonempty_iff_categoricalResidual_eq_zero
    (source : Source ⟶ Ambient) (subface : Face ⟶ Ambient)
    (injective : DegreewiseInjective subface) :
    Nonempty
        (SourceGeneratedCochainSubfaceFactorization.Factorization
          source subface) ↔
      categoricalResidual source subface = 0 := by
  constructor
  · rintro ⟨factorization⟩
    rw [categoricalResidual, ← factorization.commutes, Category.assoc,
      cokernel.condition, comp_zero]
  · intro residualZero
    exact ⟨categoricalFactorizationOfResidualZero
      source subface injective residualZero⟩

end
end SourceGeneratedCochainSubfaceCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
