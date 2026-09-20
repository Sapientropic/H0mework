import H0mework.Arithmetic.PrimeProjection.P750

/-!
# Proposition 751: a natural-coded spectral adapter covers the even source

P750 proves the unrestricted coded-descent concrete bridge is impossible and
identifies restricted/code-compatible descent as the correct mathematical
front door.  P670/P676 had already shown what the remaining source object must
be on that restricted door: an adapter whose spectral code ranges over every
ordinary even exponent.

This file constructs a stronger adapter.  It ranges over every natural
exponent, not only primes or evens.  The selected spectral point for `n` stores
`n` in the analytic coordinate and chooses exact/obstructed H1 phase according
to the real additive-prime-decomposition predicate at `n`.  Consequently the
adapter satisfies the global `spectral_complete_iff`, covers every even
exponent, and supplies the P676 even support-code source for coded descent.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Natural-coded selected spectral points -/

/-- The selected H¹-spectral point for a natural exponent. -/
def naturalCodedSpectralPoint
    (n : ℕ) :
    H1SpectralProjection (1 / 2 : ℝ) where
  phase := by
    classical
    exact if HasPrimeAdditiveDecomposition n then
      exactH1SpectralProjection.phase
    else
      obstructedH1SpectralProjection.phase
  analytic := (n : ℂ)

/-- THEOREM 1: the selected natural-coded point is H¹-complete exactly when
its exponent is additively prime-decomposable. -/
theorem naturalCodedSpectralPoint_noObstruction_iff
    (n : ℕ) :
    H1SpectralNoObstructionComplete (naturalCodedSpectralPoint n) ↔
      HasPrimeAdditiveDecomposition n := by
  classical
  by_cases h : HasPrimeAdditiveDecomposition n
  · constructor
    · intro _hno
      exact h
    · intro _hcomplete
      simpa [naturalCodedSpectralPoint, h,
        H1SpectralNoObstructionComplete,
        H1SpectralProjection.consolidatedH1Obstruction,
        H1SpectralProjection.consolidatedPhase,
        exactH1SpectralProjection]
        using exactH1SpectralProjection_noObstruction
  · constructor
    · intro hno
      have hbad :
          H1SpectralNoObstructionComplete obstructedH1SpectralProjection := by
        simpa [naturalCodedSpectralPoint, h,
          H1SpectralNoObstructionComplete,
          H1SpectralProjection.consolidatedH1Obstruction,
          H1SpectralProjection.consolidatedPhase,
          obstructedH1SpectralProjection]
          using hno
      exact False.elim
        (obstructedH1SpectralProjection_not_noObstruction hbad)
    · intro hcomplete
      exact False.elim (h hcomplete)

/-- THEOREM 2: selected natural-coded spectral points are injective. -/
theorem naturalCodedSpectralPoint_injective :
    Function.Injective naturalCodedSpectralPoint := by
  intro m n h
  have hanalytic := congrArg H1SpectralProjection.analytic h
  have hcomplex : (m : ℂ) = (n : ℂ) := by
    simpa [naturalCodedSpectralPoint] using hanalytic
  exact_mod_cast hcomplex

/-! ## The natural-coded global adapter -/

/-- A spectral point is one of the selected natural-coded witnesses. -/
def NaturalCodedSpectralSelected
    (s : H1SpectralProjection (1 / 2 : ℝ)) : Prop :=
  ∃ n : ℕ, s = naturalCodedSpectralPoint n

/-- The natural-coded spectral exponent readout.

Selected points read back their natural exponent.  Other exact points fall
back to `4`; other obstructed points fall back to `0`. -/
def naturalCodedSpectralCode
    (s : H1SpectralProjection (1 / 2 : ℝ)) : ℕ :=
  by
    classical
    exact if hsel : NaturalCodedSpectralSelected s then
      Classical.choose hsel
    else if H1SpectralNoObstructionComplete s then
      4
    else
      0

/-- THEOREM 3: the code reads a selected natural-coded point as that natural. -/
theorem naturalCodedSpectralCode_point
    (n : ℕ) :
    naturalCodedSpectralCode (naturalCodedSpectralPoint n) = n := by
  classical
  unfold naturalCodedSpectralCode
  let hsel :
      NaturalCodedSpectralSelected (naturalCodedSpectralPoint n) := ⟨n, rfl⟩
  rw [dif_pos hsel]
  have hchosen :
      naturalCodedSpectralPoint n =
        naturalCodedSpectralPoint (Classical.choose hsel) :=
    Classical.choose_spec hsel
  exact (naturalCodedSpectralPoint_injective hchosen).symm

/-- THEOREM 4: the global natural code is compatible with H¹ no-obstruction. -/
theorem naturalCodedSpectralCode_complete_iff
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    HasPrimeAdditiveDecomposition (naturalCodedSpectralCode s) ↔
      H1SpectralNoObstructionComplete s := by
  classical
  unfold naturalCodedSpectralCode
  by_cases hsel : NaturalCodedSpectralSelected s
  · rw [dif_pos hsel]
    let n : ℕ := Classical.choose hsel
    have hs : s = naturalCodedSpectralPoint n :=
      Classical.choose_spec hsel
    exact
      (naturalCodedSpectralPoint_noObstruction_iff n).symm.trans
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

/-- DEFINITION 1: the concrete natural-coded spectral exponent adapter. -/
def naturalCodedSpectralExponentAdapter :
    SpectralExponentCodeAdapter where
  code := naturalCodedSpectralCode
  spectral_complete_iff := naturalCodedSpectralCode_complete_iff

/-- A spectral exponent adapter ranges over every natural exponent. -/
def SpectralExponentNaturalCodeSurjective
    (A : SpectralExponentCodeAdapter) : Prop :=
  ∀ n : ℕ, ∃ s : H1SpectralProjection (1 / 2 : ℝ), A.code s = n

/-- THEOREM 5: the natural-coded adapter ranges over every natural exponent. -/
theorem naturalCodedSpectralExponentAdapter_naturalRange :
    SpectralExponentNaturalCodeSurjective
      naturalCodedSpectralExponentAdapter := by
  intro n
  refine ⟨naturalCodedSpectralPoint n, ?_⟩
  exact naturalCodedSpectralCode_point n

/-- THEOREM 6: natural range implies even range. -/
theorem SpectralExponentEvenCodeSurjective_of_naturalRange
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentNaturalCodeSurjective A) :
    SpectralExponentEvenCodeSurjective A := by
  intro n _hn
  exact hrange (2 * n)

/-- THEOREM 7: the natural-coded adapter covers every ordinary even exponent.
-/
theorem naturalCodedSpectralExponentAdapter_evenRange :
    SpectralExponentEvenCodeSurjective
      naturalCodedSpectralExponentAdapter :=
  SpectralExponentEvenCodeSurjective_of_naturalRange
    naturalCodedSpectralExponentAdapter
    naturalCodedSpectralExponentAdapter_naturalRange

/-! ## Even support-code source and pullback normal form -/

/-- DEFINITION 2: the P676 even support-code source supplied by the
natural-coded adapter. -/
def naturalCodedEvenSupportCodeSource :
    EvenSupportCodeSource :=
  codedDescentEvenSupportCodeSource
    naturalCodedSpectralExponentAdapter
    naturalCodedSpectralExponentAdapter_evenRange

/-- THEOREM 8: for the natural-coded adapter, the actual coded-descent
Euler-pullback representative producer is equivalent to ordinary even
Goldbach. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachStatement := by
  exact
    (evenGoldbach_iff_codedDescentEulerPullbackRepresentativeProducer_of_adapterEvenCodeRange
      naturalCodedSpectralExponentAdapter
      naturalCodedSpectralExponentAdapter_evenRange).symm

/-- THEOREM 9: the source-level P676 producer for the natural-coded adapter is
also equivalent to ordinary even Goldbach. -/
theorem naturalCodedEvenSupportCodeSource_pullbackProducer_iff_goldbach :
    Nonempty naturalCodedEvenSupportCodeSource.PullbackProducer ↔
      EvenGoldbachStatement :=
  codedDescentEvenSupportCodeSource_pullbackProducer_iff_goldbach
    naturalCodedSpectralExponentAdapter
    naturalCodedSpectralExponentAdapter_evenRange

/-! ## Packaged certificate -/

/-- P751 certificate: a concrete natural-coded spectral adapter supplies the
even support-code source required by the restricted coded-descent front door.
-/
structure NaturalCodedEvenSourceProducerCertificate where
  adapter : SpectralExponentCodeAdapter
  selected_point : ℕ -> H1SpectralProjection (1 / 2 : ℝ)
  selected_point_complete_iff :
    ∀ n : ℕ,
      H1SpectralNoObstructionComplete (selected_point n) ↔
        HasPrimeAdditiveDecomposition n
  selected_point_injective : Function.Injective selected_point
  natural_range : SpectralExponentNaturalCodeSurjective adapter
  even_range : SpectralExponentEvenCodeSurjective adapter
  source : EvenSupportCodeSource
  source_pullback_iff_goldbach :
    Nonempty source.PullbackProducer ↔ EvenGoldbachStatement
  coded_descent_producer_iff_goldbach :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer adapter) ↔
      EvenGoldbachStatement

/-- THEOREM 10: canonical P751 natural-coded even-source producer. -/
def naturalCodedEvenSourceProducerCertificate :
    NaturalCodedEvenSourceProducerCertificate where
  adapter := naturalCodedSpectralExponentAdapter
  selected_point := naturalCodedSpectralPoint
  selected_point_complete_iff :=
    naturalCodedSpectralPoint_noObstruction_iff
  selected_point_injective := naturalCodedSpectralPoint_injective
  natural_range := naturalCodedSpectralExponentAdapter_naturalRange
  even_range := naturalCodedSpectralExponentAdapter_evenRange
  source := naturalCodedEvenSupportCodeSource
  source_pullback_iff_goldbach :=
    naturalCodedEvenSupportCodeSource_pullbackProducer_iff_goldbach
  coded_descent_producer_iff_goldbach :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The unified root after P751: the restricted coded-descent route has a
concrete natural-coded even-source producer. -/
structure NaturalCodedEvenSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p750_root :
    CodedDescentRestrictedHolyGrailRootCertificate E
  natural_even_source :
    NaturalCodedEvenSourceProducerCertificate
  natural_range :
    SpectralExponentNaturalCodeSurjective naturalCodedSpectralExponentAdapter
  even_range :
    SpectralExponentEvenCodeSurjective naturalCodedSpectralExponentAdapter
  natural_source_pullback_iff_goldbach :
    Nonempty naturalCodedEvenSupportCodeSource.PullbackProducer ↔
      EvenGoldbachStatement
  natural_coded_descent_producer_iff_goldbach :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachStatement
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 11: root certificate with the natural-coded even-source producer. -/
def naturalCodedEvenSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    NaturalCodedEvenSourceUnifiedRootCertificate E where
  p750_root := codedDescentRestrictedHolyGrailRootCertificate (E := E)
  natural_even_source := naturalCodedEvenSourceProducerCertificate
  natural_range := naturalCodedSpectralExponentAdapter_naturalRange
  even_range := naturalCodedSpectralExponentAdapter_evenRange
  natural_source_pullback_iff_goldbach :=
    naturalCodedEvenSupportCodeSource_pullbackProducer_iff_goldbach
  natural_coded_descent_producer_iff_goldbach :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach
  alpha_s_residual :=
    (codedDescentRestrictedHolyGrailRootCertificate
      (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
