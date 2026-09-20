import H0mework.Arithmetic.PrimeShadow.P748

/-!
# Proposition 749: a prime-coded spectral producer for the P748 range seam

P748 normalized full coded-descent prime realization into two producer
obligations: a concrete coded-descent bridge and spectral prime-code range.

This file discharges the second obligation by constructing a concrete spectral
code adapter.  The selected spectral point for a prime exponent stores that
prime in the analytic coordinate and chooses its H¹ phase from the actual
additive-completeness predicate:

* additive-complete exponents get the exact H¹ phase;
* non-additive exponents get the obstructed H¹ phase.

For arbitrary non-selected spectral points, the adapter uses the already-known
truth values at `4` and `0` as the no-obstruction / obstruction fallback.  Thus
`spectral_complete_iff` remains global, while every prime exponent is hit by a
canonical selected spectral point.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Two small additive-completeness anchors -/

/-- THEOREM 1: `4` has the additive prime decomposition `2 + 2`. -/
theorem hasPrimeAdditiveDecomposition_four :
    HasPrimeAdditiveDecomposition 4 := by
  exact ⟨primeTwo, primeTwo, by norm_num [primeTwo]⟩

/-- THEOREM 2: `0` has no additive prime decomposition. -/
theorem not_hasPrimeAdditiveDecomposition_zero :
    Not (HasPrimeAdditiveDecomposition 0) := by
  rintro ⟨p, q, hsum⟩
  have hp : 2 ≤ p.1 := Nat.Prime.two_le p.2
  have hq : 2 ≤ q.1 := Nat.Prime.two_le q.2
  omega

/-! ## Prime-coded selected spectral points -/

/-- The selected H¹-spectral point for a prime exponent.

The analytic coordinate carries the prime exponent itself.  The phase chooses
the exact or obstructed H¹ witness according to the real additive-completeness
predicate at that exponent. -/
def primeCodedSpectralPoint
    (p : PrimeExponent) :
    H1SpectralProjection (1 / 2 : ℝ) where
  phase := by
    classical
    exact if HasPrimeAdditiveDecomposition p.1 then
      exactH1SpectralProjection.phase
    else
      obstructedH1SpectralProjection.phase
  analytic := (p.1 : ℂ)

/-- THEOREM 3: the selected point is H¹-complete exactly when its prime
exponent is additively complete. -/
theorem primeCodedSpectralPoint_noObstruction_iff
    (p : PrimeExponent) :
    H1SpectralNoObstructionComplete (primeCodedSpectralPoint p) ↔
      HasPrimeAdditiveDecomposition p.1 := by
  classical
  by_cases h : HasPrimeAdditiveDecomposition p.1
  · constructor
    · intro _hno
      exact h
    · intro _hcomplete
      simpa [primeCodedSpectralPoint, h,
        H1SpectralNoObstructionComplete,
        H1SpectralProjection.consolidatedH1Obstruction,
        H1SpectralProjection.consolidatedPhase,
        exactH1SpectralProjection]
        using exactH1SpectralProjection_noObstruction
  · constructor
    · intro hno
      have hbad :
          H1SpectralNoObstructionComplete obstructedH1SpectralProjection := by
        simpa [primeCodedSpectralPoint, h,
          H1SpectralNoObstructionComplete,
          H1SpectralProjection.consolidatedH1Obstruction,
          H1SpectralProjection.consolidatedPhase,
          obstructedH1SpectralProjection]
          using hno
      exact False.elim
        (obstructedH1SpectralProjection_not_noObstruction hbad)
    · intro hcomplete
      exact False.elim (h hcomplete)

/-- THEOREM 4: selected prime-coded spectral points are injective. -/
theorem primeCodedSpectralPoint_injective :
    Function.Injective primeCodedSpectralPoint := by
  intro p q h
  apply Subtype.ext
  have hanalytic := congrArg H1SpectralProjection.analytic h
  have hcomplex : (p.1 : ℂ) = (q.1 : ℂ) := by
    simpa [primeCodedSpectralPoint] using hanalytic
  exact_mod_cast hcomplex

/-! ## The global adapter code -/

/-- A spectral point is one of the selected prime-coded witnesses. -/
def PrimeCodedSpectralSelected
    (s : H1SpectralProjection (1 / 2 : ℝ)) : Prop :=
  ∃ p : PrimeExponent, s = primeCodedSpectralPoint p

/-- The prime-coded spectral exponent readout.

Selected prime-coded points read back their prime.  Other exact points fall
back to `4`; other obstructed points fall back to `0`. -/
def primeCodedSpectralCode
    (s : H1SpectralProjection (1 / 2 : ℝ)) : ℕ :=
  by
    classical
    exact if hsel : PrimeCodedSpectralSelected s then
    (Classical.choose hsel).1
  else if H1SpectralNoObstructionComplete s then
    4
  else
    0

/-- THEOREM 5: the code reads a selected prime-coded point as that prime. -/
theorem primeCodedSpectralCode_primePoint
    (p : PrimeExponent) :
    primeCodedSpectralCode (primeCodedSpectralPoint p) = p.1 := by
  classical
  unfold primeCodedSpectralCode
  let hsel :
      PrimeCodedSpectralSelected (primeCodedSpectralPoint p) := ⟨p, rfl⟩
  rw [dif_pos hsel]
  have hchosen :
      primeCodedSpectralPoint p =
        primeCodedSpectralPoint (Classical.choose hsel) :=
    Classical.choose_spec hsel
  have hp : p = Classical.choose hsel :=
    primeCodedSpectralPoint_injective hchosen
  exact (congrArg Subtype.val hp).symm

/-- THEOREM 6: the global code is compatible with H¹ no-obstruction. -/
theorem primeCodedSpectralCode_complete_iff
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    HasPrimeAdditiveDecomposition (primeCodedSpectralCode s) ↔
      H1SpectralNoObstructionComplete s := by
  classical
  unfold primeCodedSpectralCode
  by_cases hsel : PrimeCodedSpectralSelected s
  · rw [dif_pos hsel]
    let p : PrimeExponent := Classical.choose hsel
    have hs : s = primeCodedSpectralPoint p := Classical.choose_spec hsel
    exact
      (primeCodedSpectralPoint_noObstruction_iff p).symm.trans
        (by rw [hs])
  · rw [dif_neg hsel]
    by_cases hno : H1SpectralNoObstructionComplete s
    · rw [if_pos hno]
      constructor
      · intro _hcomplete
        exact hno
      · intro _hno
        exact hasPrimeAdditiveDecomposition_four
    · rw [if_neg hno]
      constructor
      · intro hcomplete
        exact False.elim
          (not_hasPrimeAdditiveDecomposition_zero hcomplete)
      · intro hs
        exact False.elim (hno hs)

/-- DEFINITION 1: the concrete prime-coded spectral exponent adapter. -/
def primeCodedSpectralExponentAdapter :
    SpectralExponentCodeAdapter where
  code := primeCodedSpectralCode
  spectral_complete_iff := primeCodedSpectralCode_complete_iff

/-- THEOREM 7: the prime-coded adapter ranges over every prime exponent. -/
theorem primeCodedSpectralExponentAdapter_primeRange :
    SpectralExponentPrimeCodeSurjective
      primeCodedSpectralExponentAdapter := by
  intro p
  refine ⟨primeCodedSpectralPoint p, ?_⟩
  exact primeCodedSpectralCode_primePoint p

/-! ## P748 specialized to the prime-coded adapter -/

/-- THEOREM 8: for the prime-coded adapter, P748's full realization gate has
only the concrete coded-descent bridge left. -/
theorem primeCodedPrimeIndexedRealization_iff_concreteBridge :
    Nonempty
        (PrimeIndexedShadowRealization
          (codedDescentEulerPrimeCouplingProducer
            primeCodedSpectralExponentAdapter)) ↔
      Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
          (codedDescentEulerPrimeCouplingProducer
            primeCodedSpectralExponentAdapter)) := by
  constructor
  · intro hreal
    exact
      (codedDescentPrimeIndexedRealization_iff_concreteBridge_and_primeRange
        primeCodedSpectralExponentAdapter).mp hreal |>.1
  · intro hconcrete
    exact
      (codedDescentPrimeIndexedRealization_iff_concreteBridge_and_primeRange
        primeCodedSpectralExponentAdapter).mpr
        ⟨hconcrete, primeCodedSpectralExponentAdapter_primeRange⟩

/-! ## Packaged certificate -/

/-- P749 packages the prime-coded spectral producer for P748's range seam. -/
structure PrimeCodedSpectralRangeProducerCertificate where
  adapter : SpectralExponentCodeAdapter
  selected_point :
    PrimeExponent -> H1SpectralProjection (1 / 2 : ℝ)
  selected_point_complete_iff :
    ∀ p : PrimeExponent,
      H1SpectralNoObstructionComplete (selected_point p) ↔
        HasPrimeAdditiveDecomposition p.1
  selected_point_injective :
    Function.Injective selected_point
  prime_range :
    SpectralExponentPrimeCodeSurjective adapter
  full_realization_iff_concrete_bridge :
    Nonempty
        (PrimeIndexedShadowRealization
          (codedDescentEulerPrimeCouplingProducer adapter)) ↔
      Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
          (codedDescentEulerPrimeCouplingProducer adapter))

/-- THEOREM 9: the prime-coded spectral range producer certificate. -/
def primeCodedSpectralRangeProducerCertificate :
    PrimeCodedSpectralRangeProducerCertificate where
  adapter := primeCodedSpectralExponentAdapter
  selected_point := primeCodedSpectralPoint
  selected_point_complete_iff :=
    primeCodedSpectralPoint_noObstruction_iff
  selected_point_injective := primeCodedSpectralPoint_injective
  prime_range := primeCodedSpectralExponentAdapter_primeRange
  full_realization_iff_concrete_bridge :=
    primeCodedPrimeIndexedRealization_iff_concreteBridge

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The unified root with P749's concrete spectral range producer attached
under the P748 full-prime normal form. -/
structure PrimeCodedSpectralRangeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p748_root :
    CodedDescentFullPrimeRealizationUnifiedRootCertificate E
  spectral_range_producer :
    PrimeCodedSpectralRangeProducerCertificate
  full_realization_iff_concrete_bridge :
    Nonempty
        (PrimeIndexedShadowRealization
          (codedDescentEulerPrimeCouplingProducer
            spectral_range_producer.adapter)) ↔
      Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
          (codedDescentEulerPrimeCouplingProducer
            spectral_range_producer.adapter))
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 10: the current central root with the P749 spectral range producer.
-/
def primeCodedSpectralRangeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    PrimeCodedSpectralRangeUnifiedRootCertificate E where
  p748_root := codedDescentFullPrimeRealizationUnifiedRootCertificate (E := E)
  spectral_range_producer := primeCodedSpectralRangeProducerCertificate
  full_realization_iff_concrete_bridge :=
    primeCodedPrimeIndexedRealization_iff_concreteBridge
  alpha_s_residual :=
    (codedDescentFullPrimeRealizationUnifiedRootCertificate
      (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
