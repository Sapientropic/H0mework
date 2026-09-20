import H0mework.Realization.RelaxationFlow.P579

/-!
# Proposition 580: rational and interval wrappers for SOS reducer certificates

P579 defined the core proof-carrying interface:

`gap(v) = Σ k, coeff k * feature k v ^ 2`, with `coeff k ≥ 0`.

External tools usually emit either exact rational data or interval-certified
floating data.  This file gives both outputs a Lean-facing wrapper:

* exact rational SOS coefficients;
* interval coefficients with a rational lower bound certified nonnegative.

Both wrappers compile down to P579's `SumSquaresQuadraticGapCertificate`, so the
whole bridge remains:

tool certificate -> SOS certificate -> quadratic Lyapunov certificate ->
sigma-zero reducer bridge.

This is still proof-carrying checking, not optimization or SDP solving.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w z

variable {ι : Type v} [Fintype ι]

/-! ## Exact rational SOS coefficients -/

/-- Exact rational sum-of-squares certificate.  Runtime tools can emit rational
coefficients directly; Lean coerces them into real coefficients for P579. -/
structure RationalSumSquaresQuadraticGapCertificate
    (κ : Type u) [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ) where
  coeffQ : κ → ℚ
  feature : κ → (ι → ℝ) → ℝ
  coeffQ_nonneg : ∀ k, 0 ≤ coeffQ k
  gap_eq :
    ∀ v : ι → ℝ,
      quadraticEnergyGap J P q v =
        ∑ k, (coeffQ k : ℝ) * (feature k v) ^ 2

/-- THEOREM 1: rational nonnegativity transfers to real nonnegativity. -/
theorem rationalSumSquares_coeff_nonneg_real
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : RationalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    ∀ k, 0 ≤ (hcert.coeffQ k : ℝ) := by
  intro k
  exact_mod_cast hcert.coeffQ_nonneg k

/-- THEOREM 2: exact rational SOS data produces P579's core SOS certificate. -/
def rationalSumSquares_to_sumSquares
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : RationalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    SumSquaresQuadraticGapCertificate (ι := ι) κ J P q where
  coeff := fun k => (hcert.coeffQ k : ℝ)
  feature := hcert.feature
  coeff_nonneg := rationalSumSquares_coeff_nonneg_real J P q hcert
  gap_eq := hcert.gap_eq

/-- THEOREM 3: exact rational SOS data produces the quadratic Lyapunov
certificate consumed by P578. -/
theorem rationalSumSquares_to_quadraticLyapunovCertificate
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : RationalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    QuadraticLyapunovCertificate J P q := by
  exact sumSquaresQuadraticGap_to_quadraticLyapunovCertificate J P q
    (rationalSumSquares_to_sumSquares J P q hcert)

/-! ## Rational interval wrappers for approximate / floating certificates -/

/-- Interval-certified SOS coefficients.  The real coefficient may come from an
external numerical object, but Lean only needs a rational lower bound that is
nonnegative and below the coefficient.  The upper bound is retained as audit
data for checkers, though the proof of nonnegativity only needs the lower
bound. -/
structure RationalIntervalSumSquaresQuadraticGapCertificate
    (κ : Type u) [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ) where
  coeff : κ → ℝ
  lower : κ → ℚ
  upper : κ → ℚ
  feature : κ → (ι → ℝ) → ℝ
  lower_nonneg : ∀ k, 0 ≤ lower k
  lower_le_coeff : ∀ k, (lower k : ℝ) ≤ coeff k
  coeff_le_upper : ∀ k, coeff k ≤ (upper k : ℝ)
  gap_eq :
    ∀ v : ι → ℝ,
      quadraticEnergyGap J P q v =
        ∑ k, coeff k * (feature k v) ^ 2

/-- THEOREM 4: interval lower bounds certified nonnegative prove the real
coefficients are nonnegative. -/
theorem rationalIntervalSumSquares_coeff_nonneg
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert :
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    ∀ k, 0 ≤ hcert.coeff k := by
  intro k
  have hlow : 0 ≤ (hcert.lower k : ℝ) := by
    exact_mod_cast hcert.lower_nonneg k
  exact le_trans hlow (hcert.lower_le_coeff k)

/-- THEOREM 5: interval-certified SOS data produces P579's core SOS
certificate. -/
def rationalIntervalSumSquares_to_sumSquares
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert :
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    SumSquaresQuadraticGapCertificate (ι := ι) κ J P q where
  coeff := hcert.coeff
  feature := hcert.feature
  coeff_nonneg := rationalIntervalSumSquares_coeff_nonneg J P q hcert
  gap_eq := hcert.gap_eq

/-- THEOREM 6: interval-certified SOS data produces the quadratic Lyapunov
certificate consumed by P578. -/
theorem rationalIntervalSumSquares_to_quadraticLyapunovCertificate
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert :
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    QuadraticLyapunovCertificate J P q := by
  exact sumSquaresQuadraticGap_to_quadraticLyapunovCertificate J P q
    (rationalIntervalSumSquares_to_sumSquares J P q hcert)

/-! ## Direct sigma-zero bridge from rational / interval certificates -/

/-- THEOREM 7: exact rational SOS data directly yields the sigma-zero
Lyapunov contraction bridge. -/
theorem sigmaZeroRationalSumSquaresQuadraticLyapunovContraction
    {K : Type z} [Zero K] {H : Type w} [Inhabited H]
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : RationalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    LyapunovContraction
      (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
      (sigmaZeroLiftUnary (K := K) (H := H)
        (fun x : ι → ℝ => Matrix.mulVec J x))
      (q ^ 2) := by
  exact sigmaZeroSumSquaresQuadraticLyapunovContraction
    (K := K) (H := H) J P q
    (rationalSumSquares_to_sumSquares J P q hcert)

/-- THEOREM 8: interval-certified SOS data directly yields the sigma-zero
Lyapunov contraction bridge. -/
theorem sigmaZeroRationalIntervalSumSquaresQuadraticLyapunovContraction
    {K : Type z} [Zero K] {H : Type w} [Inhabited H]
    {κ : Type u} [Fintype κ]
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert :
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q) :
    LyapunovContraction
      (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
      (sigmaZeroLiftUnary (K := K) (H := H)
        (fun x : ι → ℝ => Matrix.mulVec J x))
      (q ^ 2) := by
  exact sigmaZeroSumSquaresQuadraticLyapunovContraction
    (K := K) (H := H) J P q
    (rationalIntervalSumSquares_to_sumSquares J P q hcert)

/-- A compact checker-facing bridge certificate for exact rational and
interval-certified SOS reducer outputs. -/
structure SigmaZeroRationalIntervalReducerBridgeCertificate
    (K : Type z) [Zero K] where
  rational_to_quadratic :
    ∀ {ι : Type v} [Fintype ι] {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      RationalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      QuadraticLyapunovCertificate J P q
  interval_to_quadratic :
    ∀ {ι : Type v} [Fintype ι] {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      QuadraticLyapunovCertificate J P q
  interval_sigma_zero_contraction :
    ∀ {ι : Type v} [Fintype ι] {H : Type w} [Inhabited H]
      {κ : Type u} [Fintype κ]
      (J P : Matrix ι ι ℝ) (q : ℝ),
      RationalIntervalSumSquaresQuadraticGapCertificate (ι := ι) κ J P q →
      LyapunovContraction
        (sigmaZeroPullbackEnergy (K := K) (H := H) (quadraticVDistance P))
        (sigmaZeroLiftUnary (K := K) (H := H)
          (fun x : ι → ℝ => Matrix.mulVec J x))
        (q ^ 2)

/-- THEOREM 9: the canonical rational / interval checker bridge certificate. -/
theorem sigmaZeroRationalIntervalReducerBridgeCertificate
    (K : Type z) [Zero K] :
    SigmaZeroRationalIntervalReducerBridgeCertificate K where
  rational_to_quadratic := by
    intro ι _ κ _ J P q hcert
    exact rationalSumSquares_to_quadraticLyapunovCertificate J P q hcert
  interval_to_quadratic := by
    intro ι _ κ _ J P q hcert
    exact rationalIntervalSumSquares_to_quadraticLyapunovCertificate J P q hcert
  interval_sigma_zero_contraction := by
    intro ι _ H _ κ _ J P q hcert
    exact sigmaZeroRationalIntervalSumSquaresQuadraticLyapunovContraction
      (K := K) (H := H) J P q hcert


end AffineRelaxation
end SaturationMonoid
