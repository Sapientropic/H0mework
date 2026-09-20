import H0mework.Realization.Fibres.P575
import H0mework.Realization.Observation.Cells

/-!
# Proposition 576: sigma-zero contraction feeds observable bisimulation

P575 transported metric contraction through the sigma-zero lift.  Lemma 3
turns metric contraction plus a no-tie / margin observation cell into eventual
observable equality.

This file composes those two facts.  A bounded linear reducer on the standard
carrier, once certified by `‖f‖ ≤ q`, gives a sigma-zero lifted recall/update
step whose future observations eventually agree whenever both trajectories have
the explicit geometric tail certificate into the same observation margin.

This is the bounded-linear version of the Lemma 3 bridge.  It is not the
general spectral-radius theorem and it does not generate the margin/tail
certificate; it consumes those certificates and proves the observable
bisimulation conclusion.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x

/-- THEOREM 1: a standard fixed point lifts to a sigma-zero fixed point. -/
@[simp] theorem sigmaZeroLiftContinuousLinearMap_fixed_embed
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (f : X →L[𝕜] X) {a : X} (ha : f a = a) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f
        (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) =
      sigmaZeroEmbed (K := K) (X := X) (H := HX) a := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  apply (sigmaZeroRelaxedEquiv K X HX).injective
  change sigmaZeroForget (K := K) (X := X) (H := HX)
      (sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f
        (sigmaZeroEmbed (K := K) (X := X) (H := HX) a)) =
    sigmaZeroForget (K := K) (X := X) (H := HX)
      (sigmaZeroEmbed (K := K) (X := X) (H := HX) a)
  simp [sigmaZeroForget_liftContinuousLinearMap, ha]

/-- THEOREM 2: a bounded linear standard reducer with `‖f‖ ≤ q` gives eventual
observable equality for its sigma-zero lift once both paths have certified
tails into the same observation margin. -/
theorem sigmaZeroLiftContinuousLinearMap_eventual_obs_eq_of_norm_le_margin
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (f : X →L[𝕜] X) {q ε : ℝ} {a : X}
    {O : Type x}
    {x y : SigmaRelaxedObject K X HX (0 : K)}
    {obs : SigmaRelaxedObject K X HX (0 : K) → O}
    (hq_nonneg : 0 ≤ q)
    (hnorm : ‖f‖ ≤ q)
    (ha : f a = a) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
    (hobs_margin :
      ∀ z : SigmaRelaxedObject K X HX (0 : K),
        dist z (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := X) (H := HX) a))
    → (hxtail : ∃ Nx, ∀ n, Nx ≤ n →
        q ^ n * dist x (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε)
    → (hytail : ∃ Ny, ∀ n, Ny ≤ n →
        q ^ n * dist y (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε)
    → ∃ N, ∀ n, N ≤ n →
      obs (((sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f)^[n]) x) =
        obs (((sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f)^[n]) y) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
  intro hobs_margin hxtail hytail
  exact eventual_obs_eq_of_fixed_point_margin
    (T := sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f)
    (q := q) (ε := ε)
    (z := sigmaZeroEmbed (K := K) (X := X) (H := HX) a)
    (x := x) (y := y) (obs := obs)
    hq_nonneg
    (sigmaZeroLiftContinuousLinearMap_dist_contract_of_norm_le K 𝕜 X X HX HX f q hnorm)
    (sigmaZeroLiftContinuousLinearMap_fixed_embed K 𝕜 X HX f ha)
    hobs_margin
    hxtail
    hytail

/-- A compact certificate for the bounded-linear sigma-zero Lemma 3 bridge. -/
structure SigmaZeroObservableBisimulationCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] where
  fixed_embed :
    ∀ (X : Type v) (HX : Type w) [Inhabited HX]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      (f : X →L[𝕜] X) {a : X}, f a = a →
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f
          (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) =
        sigmaZeroEmbed (K := K) (X := X) (H := HX) a
  eventual_obs :
    ∀ (X : Type v) (HX : Type w) [Inhabited HX]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      (f : X →L[𝕜] X) {q ε : ℝ} {a : X}
      {O : Type x}
      {x y : SigmaRelaxedObject K X HX (0 : K)}
      {obs : SigmaRelaxedObject K X HX (0 : K) → O},
      0 ≤ q → ‖f‖ ≤ q → f a = a →
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      letI := sigmaZeroRelaxedNormedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedNormedSpaceInst K 𝕜 X HX
      (∀ z : SigmaRelaxedObject K X HX (0 : K),
        dist z (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := X) (H := HX) a)) →
      (∃ Nx, ∀ n, Nx ≤ n →
        q ^ n * dist x (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε) →
      (∃ Ny, ∀ n, Ny ≤ n →
        q ^ n * dist y (sigmaZeroEmbed (K := K) (X := X) (H := HX) a) < ε) →
      ∃ N, ∀ n, N ≤ n →
        obs (((sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f)^[n]) x) =
          obs (((sigmaZeroLiftContinuousLinearMap K 𝕜 X X HX HX f)^[n]) y)

/-- THEOREM 3: the canonical observable-bisimulation bridge certificate. -/
theorem sigmaZeroObservableBisimulationCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    SigmaZeroObservableBisimulationCertificate K 𝕜 where
  fixed_embed := by
    intro X HX _ _ _ f a ha
    exact sigmaZeroLiftContinuousLinearMap_fixed_embed K 𝕜 X HX f ha
  eventual_obs := by
    intro X HX _ _ _ f q ε a O x y obs hq_nonneg hnorm ha
      hobs_margin hxtail hytail
    exact sigmaZeroLiftContinuousLinearMap_eventual_obs_eq_of_norm_le_margin
      K 𝕜 X HX f hq_nonneg hnorm ha hobs_margin hxtail hytail


end AffineRelaxation
end SaturationMonoid
