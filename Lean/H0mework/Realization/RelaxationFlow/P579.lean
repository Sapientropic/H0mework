import H0mework.Realization.Fibres.P578

/-!
# Proposition 579: sum-of-squares certificates produce quadratic Lyapunov certificates

P578 consumes a `QuadraticLyapunovCertificate J P q`.  Runtime and numerical
tools usually do not want to emit a raw `∀ v` proof.  They emit a certificate:
the Lyapunov energy gap is positive semidefinite, often through an LDLᵀ /
sum-of-squares decomposition.

This file gives that certificate a Lean shape.  If the gap

`q² * vᵀ P v - (Jv)ᵀ P (Jv)`

is represented as a finite sum of nonnegative coefficients times squares, then
it is nonnegative for every vector, hence it produces the quadratic Lyapunov
certificate required by P578.  The result then composes all the way to the
sigma-zero observable-bisimulation bridge.

This is not an SDP solver.  It is the proof-carrying interface an optimizer,
LDL checker, or interval certificate can target.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w z

variable {ι : Type v} [Fintype ι]

/-! ## Sum-of-squares energy-gap certificates -/

/-- The scalar Lyapunov energy gap whose nonnegativity is equivalent to the
quadratic contraction inequality. -/
def quadraticEnergyGap (J P : Matrix ι ι ℝ) (q : ℝ) (v : ι → ℝ) : ℝ :=
  q ^ 2 * quadraticForm P v - quadraticForm P (Matrix.mulVec J v)

/-- A proof-carrying sum-of-squares / LDL-style certificate for a quadratic
Lyapunov energy gap.

`feature k v` is the certified linear/scalar feature in direction `k`, and
`coeff k` is its nonnegative diagonal weight.  An LDL checker can instantiate
these with rows of `L` and diagonal entries of `D`. -/
structure SumSquaresQuadraticGapCertificate
    (κ : Type u) [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ) where
  coeff : κ → ℝ
  feature : κ → (ι → ℝ) → ℝ
  coeff_nonneg : ∀ k, 0 ≤ coeff k
  gap_eq :
    ∀ v : ι → ℝ,
      quadraticEnergyGap J P q v =
        ∑ k, coeff k * (feature k v) ^ 2

/-- THEOREM 1: a sum-of-squares gap certificate proves the raw gap is
nonnegative for every vector. -/
theorem sumSquaresQuadraticGap_nonneg
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : SumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    ∀ v : ι → ℝ, 0 ≤ quadraticEnergyGap J P q v := by
  intro v
  rw [hcert.gap_eq v]
  exact Finset.sum_nonneg (by
    intro k _
    exact mul_nonneg (hcert.coeff_nonneg k) (sq_nonneg (hcert.feature k v)))

/-- THEOREM 2: a sum-of-squares / LDL-style gap certificate produces the
quadratic Lyapunov certificate consumed by P578. -/
theorem sumSquaresQuadraticGap_to_quadraticLyapunovCertificate
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : SumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    QuadraticLyapunovCertificate J P q := by
  intro v
  have hgap := sumSquaresQuadraticGap_nonneg J P q hcert v
  unfold quadraticEnergyGap at hgap
  linarith

/-! ## Direct bridge into the sigma-zero reducer theorem -/

/-- THEOREM 3: a sum-of-squares / LDL-style certificate directly yields the
sigma-zero quadratic reducer bridge. -/
theorem sigmaZeroSumSquaresQuadraticLyapunovContraction
    {K : Type z} [Zero K] {H : Type w} [Inhabited H]
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : SumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    LyapunovContraction
      (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
      (sigmaZeroLiftUnary (K := K) (H := H)
        (fun x : ι → ℝ => Matrix.mulVec J x))
      (q ^ 2) := by
  exact sigmaZeroQuadraticLyapunovContraction (K := K) (H := H) J P q
    (sumSquaresQuadraticGap_to_quadraticLyapunovCertificate J P q hcert)

/-- THEOREM 4: a sum-of-squares / LDL-style certificate, together with the
usual fixed-point and margin/tail certificates, gives eventual observation
equality for the sigma-zero lifted matrix reducer. -/
theorem sigmaZeroSumSquaresQuadratic_eventual_obs_eq
    {K : Type z} [Zero K] {H : Type w} [Inhabited H]
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) {q ε : ℝ} {a : ι → ℝ}
    {O : Type z}
    {x y : SigmaRelaxedObject K (ι → ℝ) H (0 : K)}
    {obs : SigmaRelaxedObject K (ι → ℝ) H (0 : K) → O}
    (hcert : SumSquaresQuadraticGapCertificate (ι := ι) κ J P q)
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
  exact sigmaZeroQuadratic_eventual_obs_eq
    (K := K) (H := H) J P
    (sumSquaresQuadraticGap_to_quadraticLyapunovCertificate J P q hcert)
    ha hobs_margin hxtail hytail

/-- A compact proof-carrying bridge certificate for LDL/SOS runtime outputs. -/
structure SigmaZeroSumSquaresReducerBridgeCertificate
    (K : Type z) [Zero K] where
  gap_nonneg :
    ∀ {ι : Type v} [Fintype ι] {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      SumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      ∀ v : ι → ℝ, 0 ≤ quadraticEnergyGap J P q v
  quadratic_certificate :
    ∀ {ι : Type v} [Fintype ι] {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      SumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      QuadraticLyapunovCertificate J P q
  sigma_zero_contraction :
    ∀ {ι : Type v} [Fintype ι] {H : Type w} [Inhabited H]
      {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      SumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      LyapunovContraction
        (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
        (sigmaZeroLiftUnary (K := K) (H := H)
          (fun x : ι → ℝ => Matrix.mulVec J x))
        (q ^ 2)

/-- THEOREM 5: the canonical LDL/SOS reducer bridge certificate. -/
theorem sigmaZeroSumSquaresReducerBridgeCertificate
    (K : Type z) [Zero K] :
    SigmaZeroSumSquaresReducerBridgeCertificate K where
  gap_nonneg := by
    intro ι _ κ _ J P q hcert
    exact sumSquaresQuadraticGap_nonneg J P q hcert
  quadratic_certificate := by
    intro ι _ κ _ J P q hcert
    exact sumSquaresQuadraticGap_to_quadraticLyapunovCertificate J P q hcert
  sigma_zero_contraction := by
    intro ι _ H _ κ _ J P q hcert
    exact sigmaZeroSumSquaresQuadraticLyapunovContraction
      (K := K) (H := H) J P q hcert


end AffineRelaxation
end SaturationMonoid
