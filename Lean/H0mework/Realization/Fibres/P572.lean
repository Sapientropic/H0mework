import H0mework.Realization.Fibres.P571

/-!
# Proposition 572: sigma-zero bounded lifts preserve pointwise operator scale

P571 proved that bounded operator pipelines are transported faithfully through
the sigma-zero carrier.  This file records the pointwise metric fact underneath
that statement: applying a lifted bounded operator and then measuring norm gives
exactly the same value as applying the original bounded operator after
forgetting the headroom coordinate.

This is the scale-preservation gate needed before using sigma-zero transport
for Hamiltonian toy models, contraction certificates, or runtime Jacobian
linearizations.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y

/-! ## Pointwise norm preservation for lifted bounded operators -/

/-- THEOREM 1: a lifted bounded operator has exactly the same pointwise output
norm as the original operator applied after forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_norm_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y)
    (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ =
      ‖f (sigmaZeroForget (K := K) (X := X) (H := HX) z)‖ := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  rw [sigmaZeroRelaxed_norm_eq]
  simp [sigmaZeroForget_liftContinuousLinearMap]

/-- THEOREM 2: lifting the identity preserves the pointwise norm of every
zero-fiber vector. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_id_norm_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type x) [Inhabited HX]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX
        (ContinuousLinearMap.id 𝕜 X) z‖ = ‖z‖ := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  rw [sigmaZeroLiftContinuousLinearMap_norm_apply]
  rw [sigmaZeroRelaxed_norm_eq]
  rfl

/-- A compact scale certificate for transported bounded operators. -/
structure SigmaZeroBoundedOperatorScaleCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  pointwise_norm :
    ∀ (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
      [Inhabited HX] [Inhabited HY]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (f : X →L[𝕜] Y) (z : SigmaRelaxedObject K X HX (0 : K)),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ =
        ‖f (sigmaZeroForget (K := K) (X := X) (H := HX) z)‖
  id_norm :
    ∀ (X : Type v) (HX : Type x) [Inhabited HX]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      (z : SigmaRelaxedObject K X HX (0 : K)),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX
          (ContinuousLinearMap.id 𝕜 X) z‖ = ‖z‖

/-- THEOREM 3: the canonical pointwise scale certificate for sigma-zero
bounded-operator lifting. -/
theorem sigmaZeroBoundedOperatorScaleCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    SigmaZeroBoundedOperatorScaleCertificate K 𝕜 where
  pointwise_norm := by
    intro X Y HX HY _ _ _ _ _ _ f z
    exact sigmaZeroLiftContinuousLinearMap_norm_apply K 𝕜 X Y HX HY f z
  id_norm := by
    intro X HX _ _ _ z
    exact sigmaZeroLiftContinuousLinearMap_id_norm_apply K 𝕜 X HX z


end AffineRelaxation
end SaturationMonoid
