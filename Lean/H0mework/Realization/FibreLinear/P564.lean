import H0mework.Realization.FibreLinear.P563

/-!
# Proposition 564: sigma-zero fibers preserve exact sequences

P563 proved that kernels and ranges are reflected exactly by the zero-fiber
forgetful projection.  This file packages the homological consequence:
`range f = ker g` holds in the standard carrier if and only if it holds after
lifting `f` and `g` to the sigma-zero fibers.

Thus the zero-fiber relaxation does not merely preserve individual linear
operators.  It preserves the exactness predicate that underlies chain
complexes, constraints, conservation laws, and cohomological carriers.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Exactness compatibility -/

/-- THEOREM 1: exactness of a linear pair is equivalent to exactness of its
sigma-zero lift. -/
@[simp] theorem sigmaZeroLiftLinearMap_exact_iff
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : X →ₗ[𝕜] Y) (g : Y →ₗ[𝕜] Z) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
    LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) =
        LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) ↔
      LinearMap.range f = LinearMap.ker g := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  constructor
  · intro h
    apply Submodule.ext
    intro y
    have hmem :
        sigmaZeroEmbed (K := K) (X := Y) (H := HY) y ∈
            LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
          sigmaZeroEmbed (K := K) (X := Y) (H := HY) y ∈
            LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) := by
      rw [h]
    calc
      y ∈ LinearMap.range f ↔
          sigmaZeroEmbed (K := K) (X := Y) (H := HY) y ∈
            LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) := by
            simpa using
              (sigmaZeroLiftLinearMap_mem_range_iff
                K 𝕜 X HX Y HY f
                (sigmaZeroEmbed (K := K) (X := Y) (H := HY) y)).symm
      _ ↔ sigmaZeroEmbed (K := K) (X := Y) (H := HY) y ∈
            LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) := hmem
      _ ↔ y ∈ LinearMap.ker g := by
            simpa using
              (sigmaZeroLiftLinearMap_mem_ker_iff
                K 𝕜 Y HY Z HZ g
                (sigmaZeroEmbed (K := K) (X := Y) (H := HY) y))
  · intro h
    apply Submodule.ext
    intro y
    calc
      y ∈ LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
          sigmaZeroForget (K := K) (X := Y) (H := HY) y ∈
            LinearMap.range f := by
            exact sigmaZeroLiftLinearMap_mem_range_iff K 𝕜 X HX Y HY f y
      _ ↔ sigmaZeroForget (K := K) (X := Y) (H := HY) y ∈
            LinearMap.ker g := by
            rw [h]
      _ ↔ y ∈
            LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) := by
            exact
              (sigmaZeroLiftLinearMap_mem_ker_iff
                K 𝕜 Y HY Z HZ g y).symm

/-- A compact certificate bundling exactness reflection and preservation for
sigma-zero lifted linear pairs. -/
structure SigmaZeroExactnessCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] where
  exact_iff :
    ∀ (f : X →ₗ[𝕜] Y) (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
      LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) =
          LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g) ↔
        LinearMap.range f = LinearMap.ker g

/-- THEOREM 2: the canonical zero-fiber exactness certificate. -/
theorem sigmaZeroExactnessCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] :
    SigmaZeroExactnessCertificate K 𝕜 X HX Y HY Z HZ where
  exact_iff := by
    intro f g
    exact sigmaZeroLiftLinearMap_exact_iff K 𝕜 X HX Y HY Z HZ f g


end AffineRelaxation
end SaturationMonoid
