import H0mework.Realization.FibreLinear.P566

/-!
# Proposition 567: lifted kernels and ranges are pullbacks of standard submodules

P563 proved pointwise membership equivalences for lifted kernels and ranges.
P566 built quotient modules by pulling standard submodules back along the
zero-fiber equivalence.  This file welds those statements:

* the range of a lifted map is exactly the pullback of the standard range;
* the kernel of a lifted map is exactly the pullback of the standard kernel.

So the quotient equivalence from P566 can be read directly with the concrete
runtime submodules produced by lifted maps.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Concrete lifted submodules are pullbacks -/

/-- THEOREM 1: the range of a sigma-zero lifted map is the pullback of the
standard range along the zero-fiber linear equivalence. -/
@[simp] theorem sigmaZeroLiftLinearMap_range_eq_comap_range
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) =
      (LinearMap.range f).comap
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  apply Submodule.ext
  intro y
  constructor
  · intro hy
    have h :=
      (sigmaZeroLiftLinearMap_mem_range_iff K 𝕜 X HX Y HY f y).mp hy
    simpa using h
  · intro hy
    apply
      (sigmaZeroLiftLinearMap_mem_range_iff K 𝕜 X HX Y HY f y).mpr
    simpa using hy

/-- THEOREM 2: the kernel of a sigma-zero lifted map is the pullback of the
standard kernel along the zero-fiber linear equivalence. -/
@[simp] theorem sigmaZeroLiftLinearMap_ker_eq_comap_ker
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (g : Y →ₗ[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) =
      (LinearMap.ker g).comap
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  apply Submodule.ext
  intro y
  constructor
  · intro hy
    have h :=
      (sigmaZeroLiftLinearMap_mem_ker_iff K 𝕜 Y HY Z HZ g y).mp hy
    simpa using h
  · intro hy
    apply
      (sigmaZeroLiftLinearMap_mem_ker_iff K 𝕜 Y HY Z HZ g y).mpr
    simpa using hy

/-- A compact certificate bundling the concrete submodule/pullback
identifications for sigma-zero lifted maps. -/
structure SigmaZeroConcreteSubmoduleCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] where
  range_pullback :
    ∀ (f : X →ₗ[𝕜] Y),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) =
        (LinearMap.range f).comap
          ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap)
  kernel_pullback :
    ∀ (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
      LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) =
        (LinearMap.ker g).comap
          ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap)

/-- THEOREM 3: the canonical concrete-submodule certificate. -/
theorem sigmaZeroConcreteSubmoduleCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] :
    SigmaZeroConcreteSubmoduleCertificate K 𝕜 X HX Y HY Z HZ where
  range_pullback := by
    intro f
    exact sigmaZeroLiftLinearMap_range_eq_comap_range K 𝕜 X HX Y HY f
  kernel_pullback := by
    intro g
    exact sigmaZeroLiftLinearMap_ker_eq_comap_ker K 𝕜 Y HY Z HZ g


end AffineRelaxation
end SaturationMonoid
