import H0mework.Realization.Fibres.P577

/-!
# Proposition 578: sigma-zero bridge for quadratic Jacobian certificates

P577 gives the generic Lyapunov transport bridge.  Lemma 3 already contains the
matrix-side certificate semantics:

`QuadraticLyapunovCertificate J P q`

which is the formal version of `Jᵀ P J ≤ q² P` as an energy contraction for
every vector.  This file composes those two layers into the exact theorem the
runtime reducer harness wants to consume:

* a quadratic Jacobian/Lyapunov certificate for `J`;
* a fixed point for the linearized reducer `x ↦ J *ᵥ x`;
* observation-margin and geometric-tail certificates;
* therefore eventual observation equality for the sigma-zero lifted reducer.

The theorem still consumes a certificate; it does not solve SDP generation or
prove the general spectral-radius theorem.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

variable {ι : Type v} [Fintype ι]

/-- THEOREM 1: a quadratic Jacobian certificate transports to a sigma-zero
Lyapunov contraction certificate for the lifted matrix reducer. -/
theorem sigmaZeroQuadraticLyapunovContraction
    {K : Type u} [Zero K] {H : Type w} [Inhabited H]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : QuadraticLyapunovCertificate J P q) :
    LyapunovContraction
      (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
      (sigmaZeroLiftUnary (K := K) (H := H)
        (fun x : ι → ℝ => Matrix.mulVec J x))
      (q ^ 2) := by
  exact (sigmaZeroLyapunovContraction_iff
    (K := K) (H := H) (quadraticVDistance P)
    (fun x : ι → ℝ => Matrix.mulVec J x) (q ^ 2)).2
      (quadratic_lyapunov_certificate_to_contraction J P q hcert)

/-- THEOREM 2: a quadratic Jacobian/Lyapunov certificate gives eventual
observation equality for the sigma-zero lifted linearized reducer, once the
fixed-point, margin, and tail certificates are supplied. -/
theorem sigmaZeroQuadratic_eventual_obs_eq
    {K : Type u} [Zero K] {H : Type w} [Inhabited H]
    (J P : Matrix ι ι ℝ) {q ε : ℝ} {a : ι → ℝ}
    {O : Type u}
    {x y : SigmaRelaxedObject K (ι → ℝ) H (0 : K)}
    {obs : SigmaRelaxedObject K (ι → ℝ) H (0 : K) → O}
    (hcert : QuadraticLyapunovCertificate J P q)
    (ha : Matrix.mulVec J a = a)
    (hobs_margin :
      ∀ z : SigmaRelaxedObject K (ι → ℝ) H (0 : K),
        sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) z
            (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a))
    (hxtail : ∃ Nx, ∀ n, Nx ≤ n →
      (q ^ 2) ^ n *
          sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) x
            (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε)
    (hytail : ∃ Ny, ∀ n, Ny ≤ n →
      (q ^ 2) ^ n *
          sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) y
            (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε) :
    ∃ N, ∀ n, N ≤ n →
      obs (((sigmaZeroLiftUnary (K := K) (H := H)
          (fun x : ι → ℝ => Matrix.mulVec J x))^[n]) x) =
        obs (((sigmaZeroLiftUnary (K := K) (H := H)
          (fun x : ι → ℝ => Matrix.mulVec J x))^[n]) y) := by
  exact sigmaZeroLiftUnary_eventual_obs_eq_of_lyapunov_margin
    (K := K) (H := H)
    (V := quadraticVDistance P)
    (T := fun x : ι → ℝ => Matrix.mulVec J x)
    (r := q ^ 2) (ε := ε) (a := a)
    (x := x) (y := y) (obs := obs)
    (sq_nonneg q)
    (quadratic_lyapunov_certificate_to_contraction J P q hcert)
    ha
    hobs_margin
    hxtail
    hytail

/-- A compact reducer-facing certificate: quadratic matrix certificate in,
sigma-zero observable-bisimulation bridge out. -/
structure SigmaZeroQuadraticReducerBridgeCertificate
    (K : Type u) [Zero K] where
  lyapunov_contraction :
    ∀ {ι : Type v} [Fintype ι] {H : Type w} [Inhabited H]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      QuadraticLyapunovCertificate J P q →
      LyapunovContraction
        (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
        (sigmaZeroLiftUnary (K := K) (H := H)
          (fun x : ι → ℝ => Matrix.mulVec J x))
        (q ^ 2)
  eventual_obs :
    ∀ {ι : Type v} [Fintype ι] {H : Type w} [Inhabited H]
      (J P : Matrix ι ι ℝ) {q ε : ℝ} {a : ι → ℝ}
      {O : Type u}
      {x y : SigmaRelaxedObject K (ι → ℝ) H (0 : K)}
      {obs : SigmaRelaxedObject K (ι → ℝ) H (0 : K) → O},
      QuadraticLyapunovCertificate J P q →
      Matrix.mulVec J a = a →
      (∀ z : SigmaRelaxedObject K (ι → ℝ) H (0 : K),
        sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) z
            (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a)) →
      (∃ Nx, ∀ n, Nx ≤ n →
        (q ^ 2) ^ n *
            sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) x
              (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε) →
      (∃ Ny, ∀ n, Ny ≤ n →
        (q ^ 2) ^ n *
            sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P) y
              (sigmaZeroEmbed (K := K) (X := ι → ℝ) (H := H) a) < ε) →
      ∃ N, ∀ n, N ≤ n →
        obs (((sigmaZeroLiftUnary (K := K) (H := H)
            (fun x : ι → ℝ => Matrix.mulVec J x))^[n]) x) =
          obs (((sigmaZeroLiftUnary (K := K) (H := H)
            (fun x : ι → ℝ => Matrix.mulVec J x))^[n]) y)

/-- THEOREM 3: the canonical sigma-zero quadratic reducer bridge certificate. -/
theorem sigmaZeroQuadraticReducerBridgeCertificate
    (K : Type u) [Zero K] :
    SigmaZeroQuadraticReducerBridgeCertificate K where
  lyapunov_contraction := by
    intro ι _ H _ J P q hcert
    exact sigmaZeroQuadraticLyapunovContraction (K := K) (H := H) J P q hcert
  eventual_obs := by
    intro ι _ H _ J P q ε a O x y obs hcert ha
      hobs_margin hxtail hytail
    exact sigmaZeroQuadratic_eventual_obs_eq
      (K := K) (H := H) J P hcert ha hobs_margin hxtail hytail


end AffineRelaxation
end SaturationMonoid
