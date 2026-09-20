import H0mework.Realization.Fibres.P562

/-!
# Proposition 563: sigma-zero lifted maps preserve kernels and ranges

P562 showed that finite endomorphism invariants are unchanged at the zero
fiber.  This file records the structural linear-map counterpart:

* a vector is in the kernel of a lifted map iff its forgetful projection is in
  the kernel of the standard map;
* a zero-fiber vector is in the range of a lifted map iff its forgetful
  projection is in the range of the standard map.

Thus zero-fiber headroom adds no hidden null directions and no hidden image
directions.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w v₂ w₂

/-! ## Kernel and range compatibility -/

@[simp] theorem sigmaZeroForget_zero
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommMonoid X] [Module 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    sigmaZeroForget (K := K) (X := X) (H := HX)
        (0 : SigmaRelaxedObject K X HX (0 : K)) = (0 : X) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  exact (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).map_zero

/-- THEOREM 1: kernel membership of a lifted map is exactly kernel membership
after forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroLiftLinearMap_mem_ker_iff
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y)
    (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    z ∈ LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
      sigmaZeroForget (K := K) (X := X) (H := HX) z ∈ LinearMap.ker f := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  constructor
  · intro hz
    have h0Y :
        sigmaZeroForget (K := K) (X := Y) (H := HY)
            (0 : SigmaRelaxedObject K Y HY (0 : K)) = (0 : Y) :=
      sigmaZeroForget_zero K 𝕜 Y HY
    have hforget := congrArg
      (sigmaZeroForget (K := K) (X := Y) (H := HY)) hz
    simpa [h0Y] using hforget
  · intro hz
    have h0Y :
        sigmaZeroForget (K := K) (X := Y) (H := HY)
            (0 : SigmaRelaxedObject K Y HY (0 : K)) = (0 : Y) :=
      sigmaZeroForget_zero K 𝕜 Y HY
    apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).injective
    change
      sigmaZeroForget (K := K) (X := Y) (H := HY)
          (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f z) =
        sigmaZeroForget (K := K) (X := Y) (H := HY)
          (0 : SigmaRelaxedObject K Y HY (0 : K))
    simpa [sigmaZeroForget_liftLinearMap, h0Y] using hz

/-- THEOREM 2: range membership of a lifted map is exactly range membership
after forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroLiftLinearMap_mem_range_iff
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (f : X →ₗ[𝕜] Y)
    (y : SigmaRelaxedObject K Y HY (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    y ∈ LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
      sigmaZeroForget (K := K) (X := Y) (H := HY) y ∈ LinearMap.range f := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨sigmaZeroForget (K := K) (X := X) (H := HX) z,
      by simp [sigmaZeroForget_liftLinearMap]⟩
  · rintro ⟨x, hx⟩
    refine ⟨sigmaZeroEmbed (K := K) (X := X) (H := HX) x, ?_⟩
    apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Y HY).injective
    simp [sigmaZeroForget_liftLinearMap, hx]

/-- A compact certificate bundling kernel and range reflection for zero-fiber
lifted maps. -/
structure SigmaZeroKernelRangeCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] where
  kernel :
    ∀ (f : X →ₗ[𝕜] Y)
      (z : SigmaRelaxedObject K X HX (0 : K)),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      z ∈ LinearMap.ker (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
        sigmaZeroForget (K := K) (X := X) (H := HX) z ∈ LinearMap.ker f
  range :
    ∀ (f : X →ₗ[𝕜] Y)
      (y : SigmaRelaxedObject K Y HY (0 : K)),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      y ∈ LinearMap.range (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) ↔
        sigmaZeroForget (K := K) (X := Y) (H := HY) y ∈ LinearMap.range f

/-- THEOREM 3: the canonical zero-fiber kernel/range certificate. -/
theorem sigmaZeroKernelRangeCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] :
    SigmaZeroKernelRangeCertificate K 𝕜 X HX Y HY where
  kernel := by
    intro f z
    exact sigmaZeroLiftLinearMap_mem_ker_iff K 𝕜 X HX Y HY f z
  range := by
    intro f y
    exact sigmaZeroLiftLinearMap_mem_range_iff K 𝕜 X HX Y HY f y


end AffineRelaxation
end SaturationMonoid
