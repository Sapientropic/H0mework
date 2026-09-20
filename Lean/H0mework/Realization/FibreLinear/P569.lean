import H0mework.Realization.FibreLinear.P568

/-!
# Proposition 569: concrete quotient degrees of freedom are preserved

P568 built concrete quotient equivalences for lifted ranges and kernels.  This
file projects those object-level equivalences down to finite-dimensional
degrees of freedom: after quotienting by the concrete lifted range/kernel, the
sigma-zero carrier has the same `finrank` as the corresponding standard
quotient.

This is the quotient-level freedom-counting bridge for constraint reduction,
gauge reduction, and homological quotient carriers.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Quotient finrank compatibility -/

/-- THEOREM 1: quotienting by a concrete lifted range preserves finite degrees
of freedom. -/
@[simp] theorem sigmaZeroRangeQuotient_finrank_eq
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    Module.finrank 𝕜
        (SigmaRelaxedObject K Y HY (0 : K) ⧸
          LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f)) =
      Module.finrank 𝕜 (Y ⧸ LinearMap.range f) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  exact (sigmaZeroRangeQuotientLinearEquiv K 𝕜 X HX Y HY f).finrank_eq

/-- THEOREM 2: quotienting by a concrete lifted kernel preserves finite degrees
of freedom. -/
@[simp] theorem sigmaZeroKernelQuotient_finrank_eq
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z]
    (g : Y →ₗ[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    Module.finrank 𝕜
        (SigmaRelaxedObject K Y HY (0 : K) ⧸
          LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g)) =
      Module.finrank 𝕜 (Y ⧸ LinearMap.ker g) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  exact (sigmaZeroKernelQuotientLinearEquiv K 𝕜 Y HY Z HZ g).finrank_eq

/-- A compact certificate bundling quotient-level finite-degree preservation. -/
structure SigmaZeroQuotientFinrankCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z] where
  range_quotient_finrank :
    ∀ (f : X →ₗ[𝕜] Y),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      Module.finrank 𝕜
          (SigmaRelaxedObject K Y HY (0 : K) ⧸
            LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f)) =
        Module.finrank 𝕜 (Y ⧸ LinearMap.range f)
  kernel_quotient_finrank :
    ∀ (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedAddCommGroupInst K Z HZ
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
      Module.finrank 𝕜
          (SigmaRelaxedObject K Y HY (0 : K) ⧸
            LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g)) =
        Module.finrank 𝕜 (Y ⧸ LinearMap.ker g)

/-- THEOREM 3: the canonical quotient-finrank certificate. -/
theorem sigmaZeroQuotientFinrankCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z] :
    SigmaZeroQuotientFinrankCertificate K 𝕜 X HX Y HY Z HZ where
  range_quotient_finrank := by
    intro f
    exact sigmaZeroRangeQuotient_finrank_eq K 𝕜 X HX Y HY f
  kernel_quotient_finrank := by
    intro g
    exact sigmaZeroKernelQuotient_finrank_eq K 𝕜 Y HY Z HZ g


end AffineRelaxation
end SaturationMonoid
