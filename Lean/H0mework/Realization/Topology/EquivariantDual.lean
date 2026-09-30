import H0mework.Realization.Topology.DualExtension

/-!
# Equivariant generalized-dual extension disposition

For an actual Hilbert action and character, continuous eigenfunctionals form
a canonical submodule of the Hilbert dual. Restriction to the source test
carrier therefore has an exact quotient residual. Its zero fibre is exactly
the existence of a bounded equivariant extension.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Defect from the eigenfunctional law for the actual Hilbert action. -/
def hilbertEigenDefect
    (action : H →L[ℂ] H) (character : ℂ) :
    HilbertDual H →ₗ[ℂ] HilbertDual H where
  toFun functional := functional.comp action - character • functional
  map_add' left right := by
    ext value
    simp
    ring
  map_smul' scalar functional := by
    ext value
    simp
    ring

abbrev HilbertEigenDual
    (action : H →L[ℂ] H) (character : ℂ) :=
  LinearMap.ker (hilbertEigenDefect action character)

theorem mem_hilbertEigenDual_iff
    (action : H →L[ℂ] H) (character : ℂ)
    (functional : HilbertDual H) :
    functional ∈ HilbertEigenDual action character ↔
      ∀ value : H,
        functional (action value) = character * functional value := by
  rw [LinearMap.mem_ker]
  constructor
  · intro defect_zero value
    have pointwise := congrArg
      (fun defect : HilbertDual H => defect value) defect_zero
    change functional (action value) -
        character * functional value = 0 at pointwise
    exact sub_eq_zero.mp pointwise
  · intro eigenlaw
    apply ContinuousLinearMap.ext
    intro value
    change functional (action value) -
      character * functional value = 0
    exact sub_eq_zero.mpr (eigenlaw value)

def hilbertEigenDualRestriction
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H) (character : ℂ) :
    HilbertEigenDual action character →ₗ[ℂ] TestDual C :=
  (hilbertDualRestriction feature).comp
    (HilbertEigenDual action character).subtype

abbrev EquivariantExtensionResidual
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H) (character : ℂ) :=
  TestDual C ⧸ LinearMap.range
    (hilbertEigenDualRestriction feature action character)

def canonicalEquivariantExtensionResidual
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H)
    (character : ℂ) (functional : TestDual C) :
    EquivariantExtensionResidual feature action character :=
  Submodule.Quotient.mk functional

structure EquivariantBoundedExtension
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H)
    (character : ℂ) (functional : TestDual C) where
  extension : HilbertDual H
  eigenlaw : ∀ value : H,
    extension (action value) = character * extension value
  restricts : extension.toLinearMap.comp feature = functional

def EquivariantBoundedExtension.toBoundedExtension
    {feature : C →ₗ[ℂ] H} {action : H →L[ℂ] H}
    {character : ℂ} {functional : TestDual C}
    (extension : EquivariantBoundedExtension
      feature action character functional) :
    BoundedExtension feature functional :=
  ⟨extension.extension, extension.restricts⟩

theorem EquivariantBoundedExtension.unique_of_denseRange
    {feature : C →ₗ[ℂ] H} {action : H →L[ℂ] H}
    {character : ℂ} {functional : TestDual C}
    (dense : DenseRange feature)
    (left right : EquivariantBoundedExtension
      feature action character functional) :
    left = right := by
  have extension_eq : left.extension = right.extension := congrArg
    BoundedExtension.extension
    (BoundedExtension.unique_of_denseRange dense
      left.toBoundedExtension right.toBoundedExtension)
  cases left
  cases right
  cases extension_eq
  rfl

theorem canonicalEquivariantExtensionResidual_eq_zero_iff
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H)
    (character : ℂ) (functional : TestDual C) :
    canonicalEquivariantExtensionResidual feature action character
        functional = 0 ↔
      Nonempty (EquivariantBoundedExtension
        feature action character functional) := by
  rw [canonicalEquivariantExtensionResidual,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨extension, restricts⟩
    change extension.1.toLinearMap.comp feature = functional at restricts
    refine ⟨⟨extension.1, ?_, restricts⟩⟩
    exact (mem_hilbertEigenDual_iff action character extension.1).mp
      extension.2
  · rintro ⟨⟨extension, eigenlaw, restricts⟩⟩
    refine ⟨⟨extension,
      (mem_hilbertEigenDual_iff action character extension).mpr eigenlaw⟩,
      ?_⟩
    change extension.toLinearMap.comp feature = functional
    exact restricts

inductive EquivariantExtensionDisposition
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H)
    (character : ℂ) (functional : TestDual C)
  | bounded (extensions : Nonempty (EquivariantBoundedExtension
      feature action character functional))
  | residual (coordinate_ne_zero :
      canonicalEquivariantExtensionResidual
        feature action character functional ≠ 0)

/-- Total equivariant-extension or explicit-residual disposition. -/
def settleEquivariantExtension
    (feature : C →ₗ[ℂ] H) (action : H →L[ℂ] H)
    (character : ℂ) (functional : TestDual C) :
    EquivariantExtensionDisposition feature action character functional := by
  classical
  by_cases exists_extension : Nonempty (EquivariantBoundedExtension
      feature action character functional)
  · exact .bounded exists_extension
  · exact .residual (fun coordinate_zero =>
      exists_extension
        ((canonicalEquivariantExtensionResidual_eq_zero_iff
          feature action character functional).mp coordinate_zero))

end

end SourceGeneratedTestHilbertGeneralizedDual
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
