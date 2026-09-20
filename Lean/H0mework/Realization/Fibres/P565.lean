import H0mework.Realization.FibreLinear.P564

/-!
# Proposition 565: sigma-zero fibers preserve chain-complex equations

P564 preserved exactness (`range f = ker g`).  The other structural half of a
chain complex is the equation `g ∘ f = 0`.  This file proves that the equation
is true after lifting to sigma-zero fibers if and only if it is true in the
standard carrier.

Together with P564, this is the zero-fiber homological spine: cycles,
boundaries, exactness, and complex equations are not external interpretations
of the saturation construction.  They are preserved and reflected by the
sigma-zero projection itself.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v₁ v₂ v₃ w₁ w₂ w₃

/-! ## Chain-complex equation compatibility -/

/-- THEOREM 1: the equation `g ∘ f = 0` is equivalent to the corresponding
equation for sigma-zero lifted maps. -/
@[simp] theorem sigmaZeroLiftLinearMap_comp_eq_zero_iff
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
    (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g).comp
        (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) = 0 ↔
      g.comp f = 0 := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have h0Z :
        sigmaZeroForget (K := K) (X := Z) (H := HZ)
            (0 : SigmaRelaxedObject K Z HZ (0 : K)) = (0 : Z) :=
      sigmaZeroForget_zero K 𝕜 Z HZ
    have hpoint := congrArg
      (fun F :
          SigmaRelaxedObject K X HX (0 : K) →ₗ[𝕜]
            SigmaRelaxedObject K Z HZ (0 : K) =>
        sigmaZeroForget (K := K) (X := Z) (H := HZ)
          (F (sigmaZeroEmbed (K := K) (X := X) (H := HX) x))) h
    simpa [LinearMap.comp_apply, sigmaZeroForget_liftLinearMap, h0Z] using hpoint
  · intro h
    apply LinearMap.ext
    intro z
    have h0Z :
        sigmaZeroForget (K := K) (X := Z) (H := HZ)
            (0 : SigmaRelaxedObject K Z HZ (0 : K)) = (0 : Z) :=
      sigmaZeroForget_zero K 𝕜 Z HZ
    have hpoint := congrArg
      (fun F : X →ₗ[𝕜] Z =>
        F (sigmaZeroForget (K := K) (X := X) (H := HX) z)) h
    apply (sigmaZeroRelaxedLinearEquiv K 𝕜 Z HZ).injective
    change
      sigmaZeroForget (K := K) (X := Z) (H := HZ)
          (((sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g).comp
              (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f)) z) =
        sigmaZeroForget (K := K) (X := Z) (H := HZ)
          (0 : SigmaRelaxedObject K Z HZ (0 : K))
    simpa [LinearMap.comp_apply, sigmaZeroForget_liftLinearMap, h0Z] using hpoint

/-- A compact certificate bundling chain-complex equation reflection and
preservation for sigma-zero lifted linear pairs. -/
structure SigmaZeroChainEquationCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] where
  comp_zero_iff :
    ∀ (f : X →ₗ[𝕜] Y) (g : Y →ₗ[𝕜] Z),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommMonoidInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedAddCommMonoidInst K Z HZ
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Z HZ
      (sigmaZeroLiftLinearMap K 𝕜 Y Z HY HZ g).comp
          (sigmaZeroLiftLinearMap K 𝕜 X Y HX HY f) = 0 ↔
        g.comp f = 0

/-- THEOREM 2: the canonical zero-fiber chain-equation certificate. -/
theorem sigmaZeroChainEquationCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Semiring 𝕜]
    (X : Type v₁) (HX : Type w₁) [Inhabited HX]
    (Y : Type v₂) (HY : Type w₂) [Inhabited HY]
    (Z : Type v₃) (HZ : Type w₃) [Inhabited HZ]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z] :
    SigmaZeroChainEquationCertificate K 𝕜 X HX Y HY Z HZ where
  comp_zero_iff := by
    intro f g
    exact sigmaZeroLiftLinearMap_comp_eq_zero_iff K 𝕜 X HX Y HY Z HZ f g


end AffineRelaxation
end SaturationMonoid
