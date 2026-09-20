import H0mework.Realization.Fibres.P572

/-!
# Proposition 573: sigma-zero bounded lifts preserve operator norm

P572 proved pointwise output-norm preservation for lifted bounded operators.
This file upgrades that pointwise statement to the operator norm itself.

The proof is two-sided:

* the lifted operator is no larger, because every lifted output norm is bounded
  by the original operator norm after forgetting headroom;
* the lifted operator is no smaller, because every standard input can be tested
  inside the zero fiber via `sigmaZeroEmbed`.

Thus zero-fiber transport preserves not only bounded-operator composition, but
also the quantitative scale used by contraction, Lyapunov, and bounded
Hamiltonian certificates.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x y

/-! ## Operator norm preservation -/

/-- THEOREM 1: the sigma-zero lift of a bounded operator has the same operator
norm as the original bounded operator. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_norm
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ = ‖f‖ := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  refine ContinuousLinearMap.opNorm_eq_of_bounds
    (ContinuousLinearMap.opNorm_nonneg f) ?_ ?_
  · intro z
    calc
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f z‖ =
          ‖f (sigmaZeroForget (K := K) (X := X) (H := HX) z)‖ := by
            rw [sigmaZeroLiftContinuousLinearMap_norm_apply]
      _ ≤ ‖f‖ *
          ‖sigmaZeroForget (K := K) (X := X) (H := HX) z‖ := by
            exact f.le_opNorm _
      _ = ‖f‖ * ‖z‖ := by
            rw [sigmaZeroRelaxed_norm_eq]
  · intro N hN hbound
    apply ContinuousLinearMap.opNorm_le_bound f hN
    intro x
    have h := hbound (sigmaZeroEmbed (K := K) (X := X) (H := HX) x)
    simpa [sigmaZeroLiftContinuousLinearMap_norm_apply,
      sigmaZeroRelaxed_norm_eq] using h

/-- THEOREM 2: the sigma-zero bounded Hom equivalence preserves operator
norms. -/
@[simp] theorem sigmaZeroContinuousLinearMapEquiv_norm_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
    [Inhabited HX] [Inhabited HY]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
    ‖sigmaZeroContinuousLinearMapEquiv K 𝕜 X Y HX HY f‖ = ‖f‖ := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
  exact sigmaZeroLiftContinuousLinearMap_norm K 𝕜 X Y HX HY f

/-- A compact norm certificate for sigma-zero bounded operators. -/
structure SigmaZeroBoundedOperatorNormCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  lift_norm :
    ∀ (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
      [Inhabited HX] [Inhabited HY]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (f : X →L[𝕜] Y),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      ‖sigmaZeroLiftContinuousLinearMap K 𝕜 X Y HX HY f‖ = ‖f‖
  equiv_norm :
    ∀ (X : Type v) (Y : Type w) (HX : Type x) (HY : Type y)
      [Inhabited HX] [Inhabited HY]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (f : X →L[𝕜] Y),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      letI := sigmaZeroRelaxedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedModuleInst K 𝕜 Y HY
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K Y HY
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 Y HY
      ‖sigmaZeroContinuousLinearMapEquiv K 𝕜 X Y HX HY f‖ = ‖f‖

/-- THEOREM 3: the canonical operator-norm preservation certificate. -/
theorem sigmaZeroBoundedOperatorNormCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    SigmaZeroBoundedOperatorNormCertificate K 𝕜 where
  lift_norm := by
    intro X Y HX HY _ _ _ _ _ _ f
    exact sigmaZeroLiftContinuousLinearMap_norm K 𝕜 X Y HX HY f
  equiv_norm := by
    intro X Y HX HY _ _ _ _ _ _ f
    exact sigmaZeroContinuousLinearMapEquiv_norm_apply K 𝕜 X Y HX HY f


end AffineRelaxation
end SaturationMonoid
