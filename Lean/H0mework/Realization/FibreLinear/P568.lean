import H0mework.Realization.FibreLinear.P567

/-!
# Proposition 568: concrete lifted range/kernel quotients are standard quotients

P566 produced quotient equivalences for pullback submodules.  P567 identified
the concrete lifted range and kernel with those pullbacks.  This file composes
the two facts into directly usable quotient equivalences:

* quotient by `range (lift f)` is equivalent to quotient by `range f`;
* quotient by `ker (lift g)` is equivalent to quotient by `ker g`.

These are the object-level bridges needed by homology, gauge reduction, and
constraint quotient arguments.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Quotients by concrete lifted ranges -/

/-- Quotienting the sigma-zero target by the concrete lifted range is
canonically equivalent to quotienting the standard target by the standard
range. -/
def sigmaZeroRangeQuotientLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    (SigmaRelaxedObject K Y HY (0 : K) ⧸
        LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f)) ≃ₗ[𝕜]
      (Y ⧸ LinearMap.range f) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact
    (Submodule.quotEquivOfEq
      (LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f))
      ((LinearMap.range f).comap
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap))
      (sigmaZeroLiftLinearMap_range_eq_comap_range K 𝕜 X HX Y HY f)).trans
      (sigmaZeroQuotientLinearEquiv K 𝕜 Y HY (LinearMap.range f))

/-- THEOREM 1: the concrete range quotient equivalence acts on classes by
forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroRangeQuotientLinearEquiv_apply_mk
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y)
    (y : SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    sigmaZeroRangeQuotientLinearEquiv K 𝕜 X HX Y HY f
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (sigmaZeroForget (K := K) (X := Y) (H := HY) y) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  simp [sigmaZeroRangeQuotientLinearEquiv]

/-! ## Quotients by concrete lifted kernels -/

/-- Quotienting the sigma-zero source by the concrete lifted kernel is
canonically equivalent to quotienting the standard source by the standard
kernel. -/
def sigmaZeroKernelQuotientLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z]
    (g : Y →ₗ[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    (SigmaRelaxedObject K Y HY (0 : K) ⧸
        LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g)) ≃ₗ[𝕜]
      (Y ⧸ LinearMap.ker g) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  exact
    (Submodule.quotEquivOfEq
      (LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g))
      ((LinearMap.ker g).comap
        ((sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).toLinearMap))
      (sigmaZeroLiftLinearMap_ker_eq_comap_ker K 𝕜 Y HY Z HZ g)).trans
      (sigmaZeroQuotientLinearEquiv K 𝕜 Y HY (LinearMap.ker g))

/-- THEOREM 2: the concrete kernel quotient equivalence acts on classes by
forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroKernelQuotientLinearEquiv_apply_mk
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z]
    (g : Y →ₗ[𝕜] Z)
    (y : SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    sigmaZeroKernelQuotientLinearEquiv K 𝕜 Y HY Z HZ g
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (sigmaZeroForget (K := K) (X := Y) (H := HY) y) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  simp [sigmaZeroKernelQuotientLinearEquiv]

/-- A compact certificate bundling the concrete range/kernel quotient bridges. -/
structure SigmaZeroConcreteQuotientCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z] where
  range_quotient_equiv :
    ∀ (f : X →ₗ[𝕜] Y),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      (SigmaRelaxedObject K Y HY (0 : K) ⧸
          LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f)) ≃ₗ[𝕜]
        (Y ⧸ LinearMap.range f)
  kernel_quotient_equiv :
    ∀ (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
      (SigmaRelaxedObject K Y HY (0 : K) ⧸
          LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g)) ≃ₗ[𝕜]
        (Y ⧸ LinearMap.ker g)

/-- DEFINITION 3: the canonical concrete quotient certificate. -/
def sigmaZeroConcreteQuotientCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z] :
    SigmaZeroConcreteQuotientCertificate K 𝕜 X HX Y HY Z HZ where
  range_quotient_equiv := by
    intro f
    exact sigmaZeroRangeQuotientLinearEquiv K 𝕜 X HX Y HY f
  kernel_quotient_equiv := by
    intro g
    exact sigmaZeroKernelQuotientLinearEquiv K 𝕜 Y HY Z HZ g


end AffineRelaxation
end SaturationMonoid
