import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Source-generated test--Hilbert extension disposition

An actual algebraic test carrier may enter a Hilbert carrier through a
source-owned feature while carrying a functional that is not bounded for the
Hilbert norm. Restriction of the Hilbert continuous dual gives a canonical
subspace of the algebraic test dual. The quotient by that range is the exact
bounded-extension residual.

This kernel does not assume injectivity, density, finite dimension, or the
existence of an extension. It generates either a bounded extension or a
nonzero residual coordinate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c h q

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev TestDual (C : Type c) [AddCommGroup C] [Module ℂ C] :=
  Module.Dual ℂ C

abbrev HilbertDual (H : Type h) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  StrongDual ℂ H

/-- Restriction of bounded Hilbert functionals along the actual feature. -/
def hilbertDualRestriction (feature : C →ₗ[ℂ] H) :
    HilbertDual H →ₗ[ℂ] TestDual C where
  toFun functional := functional.toLinearMap.comp feature
  map_add' left right := by
    ext value
    rfl
  map_smul' scalar functional := by
    ext value
    rfl

@[simp] theorem hilbertDualRestriction_apply
    (feature : C →ₗ[ℂ] H) (functional : HilbertDual H) (value : C) :
    hilbertDualRestriction feature functional value =
      functional (feature value) :=
  rfl

/-- Exact coordinate measuring failure of bounded extension. -/
abbrev ExtensionResidual (feature : C →ₗ[ℂ] H) :=
  TestDual C ⧸ LinearMap.range (hilbertDualRestriction feature)

def canonicalExtensionResidual
    (feature : C →ₗ[ℂ] H) (functional : TestDual C) :
    ExtensionResidual feature :=
  Submodule.Quotient.mk functional

theorem canonicalExtensionResidual_eq_zero_iff
    (feature : C →ₗ[ℂ] H) (functional : TestDual C) :
    canonicalExtensionResidual feature functional = 0 ↔
      ∃ extension : HilbertDual H,
        extension.toLinearMap.comp feature = functional := by
  rw [canonicalExtensionResidual, Submodule.Quotient.mk_eq_zero]
  rfl

structure BoundedExtension
    (feature : C →ₗ[ℂ] H) (functional : TestDual C) where
  extension : HilbertDual H
  restricts : extension.toLinearMap.comp feature = functional

theorem BoundedExtension.kills_feature_kernel
    {feature : C →ₗ[ℂ] H} {functional : TestDual C}
    (extension : BoundedExtension feature functional) :
    LinearMap.ker feature ≤ LinearMap.ker functional := by
  intro value value_mem
  rw [LinearMap.mem_ker] at value_mem ⊢
  have readback := LinearMap.congr_fun extension.restricts value
  simpa [LinearMap.comp_apply, value_mem] using readback.symm

theorem BoundedExtension.unique_of_denseRange
    {feature : C →ₗ[ℂ] H} {functional : TestDual C}
    (dense : DenseRange feature)
    (left right : BoundedExtension feature functional) :
    left = right := by
  have extension_eq : left.extension = right.extension := by
    apply ContinuousLinearMap.ext
    intro value
    have functions_eq := dense.equalizer left.extension.continuous
      right.extension.continuous (by
        funext source
        have leftRead := LinearMap.congr_fun left.restricts source
        have rightRead := LinearMap.congr_fun right.restricts source
        exact leftRead.trans rightRead.symm)
    exact congrFun functions_eq value
  cases left
  cases right
  cases extension_eq
  rfl

theorem canonicalExtensionResidual_eq_zero_iff_nonempty
    (feature : C →ₗ[ℂ] H) (functional : TestDual C) :
    canonicalExtensionResidual feature functional = 0 ↔
      Nonempty (BoundedExtension feature functional) := by
  rw [canonicalExtensionResidual_eq_zero_iff]
  constructor
  · rintro ⟨extension, restricts⟩
    exact ⟨⟨extension, restricts⟩⟩
  · rintro ⟨⟨extension, restricts⟩⟩
    exact ⟨extension, restricts⟩

inductive ExtensionDisposition
    (feature : C →ₗ[ℂ] H) (functional : TestDual C)
  | bounded (extensions : Nonempty (BoundedExtension feature functional))
  | residual (coordinate_ne_zero :
      canonicalExtensionResidual feature functional ≠ 0)

/-- Total bounded-extension or explicit-residual disposition. -/
def settleExtension
    (feature : C →ₗ[ℂ] H) (functional : TestDual C) :
    ExtensionDisposition feature functional := by
  classical
  by_cases exists_extension : Nonempty (BoundedExtension feature functional)
  · exact .bounded exists_extension
  · exact .residual (fun coordinate_zero =>
      exists_extension
        ((canonicalExtensionResidual_eq_zero_iff_nonempty
          feature functional).mp coordinate_zero))

/-- A dense source feature makes the positive extension branch unique. -/
def canonicalBoundedExtension
    (feature : C →ₗ[ℂ] H) (functional : TestDual C)
    (_dense : DenseRange feature)
    (residual_zero : canonicalExtensionResidual feature functional = 0) :
    BoundedExtension feature functional :=
  Classical.choice
    ((canonicalExtensionResidual_eq_zero_iff_nonempty
      feature functional).mp residual_zero)

theorem canonicalBoundedExtension_unique
    (feature : C →ₗ[ℂ] H) (functional : TestDual C)
    (dense : DenseRange feature)
    (residual_zero : canonicalExtensionResidual feature functional = 0)
    (other : BoundedExtension feature functional) :
    canonicalBoundedExtension feature functional dense residual_zero = other :=
  BoundedExtension.unique_of_denseRange dense _ _

/-- A bounded extension on a complete Hilbert face has its canonical Riesz
representative. -/
def BoundedExtension.rieszRepresentative
    [CompleteSpace H]
    {feature : C →ₗ[ℂ] H} {functional : TestDual C}
    (extension : BoundedExtension feature functional) : H :=
  (InnerProductSpace.toDual ℂ H).symm extension.extension

theorem BoundedExtension.riesz_readback
    [CompleteSpace H]
    {feature : C →ₗ[ℂ] H} {functional : TestDual C}
    (extension : BoundedExtension feature functional) (value : C) :
    inner ℂ extension.rieszRepresentative (feature value) =
      functional value := by
  change inner ℂ
      ((InnerProductSpace.toDual ℂ H).symm extension.extension)
        (feature value) = functional value
  rw [InnerProductSpace.toDual_symm_apply]
  exact LinearMap.congr_fun extension.restricts value

/-! ## Universal quotient factorization -/

def residualFactor
    {Q : Type q} [AddCommGroup Q] [Module ℂ Q]
    (feature : C →ₗ[ℂ] H) (map : TestDual C →ₗ[ℂ] Q)
    (kills_extensions : LinearMap.range (hilbertDualRestriction feature) ≤
      LinearMap.ker map) :
    ExtensionResidual feature →ₗ[ℂ] Q :=
  (LinearMap.range (hilbertDualRestriction feature)).liftQ
    map kills_extensions

@[simp] theorem residualFactor_comp_mkQ
    {Q : Type q} [AddCommGroup Q] [Module ℂ Q]
    (feature : C →ₗ[ℂ] H) (map : TestDual C →ₗ[ℂ] Q)
    (kills_extensions : LinearMap.range (hilbertDualRestriction feature) ≤
      LinearMap.ker map) :
    (residualFactor feature map kills_extensions).comp
        (Submodule.mkQ (LinearMap.range
          (hilbertDualRestriction feature))) = map := by
  apply LinearMap.ext
  intro functional
  rfl

end

end SourceGeneratedTestHilbertGeneralizedDual
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
