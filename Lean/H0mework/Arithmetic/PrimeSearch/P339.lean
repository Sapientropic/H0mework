import H0mework.Arithmetic.PrimeSearch.P338

/-!
# Proposition 339: direct search transfer through the admissible pullback bridge

P325 identifies the honest remaining interface: an arithmetic-admissible
seven-facet state can be synchronized with H1 only after a concrete
prime-shadow bridge is supplied.  P338 supplies a certified direct Goldbach
search and its convolution-coefficient face.

This file connects those two pieces.  It proves that any concrete admissible
prime-shadow bridge automatically transfers the P338 direct computation
surface to the H1 no-obstruction surface.

Boundary: this still does not construct the missing prime-shadow producer.
It says exactly what the direct algorithm buys once such a producer exists.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Direct search on an admissible seven-facet state -/

/-- THEOREM 1: on an arithmetic-admissible state, direct search at the chosen
arithmetic exponent is exactly raw-rate half-sigma Goldbach for that state. -/
theorem admissibleDirectSearch_iff_rateGoldbach
    (x : ArithmeticAdmissibleSevenFacet) :
    (goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic)).isSome =
        true ↔
      HalfSigmaRateGoldbachComplete x.val.rate := by
  have hrate : (x.arithmetic).1 = x.val.rate :=
    ArithmeticAdmissibleSevenFacet.arithmetic_rate_eq x
  have himage :
      HalfSigmaRateGoldbachComplete x.val.rate ↔
        HalfSigmaImageGoldbachComplete x.arithmetic := by
    rw [← hrate]
    exact halfSigmaRateGoldbachComplete_of_image x.arithmetic
  exact
    (goldbachDirectSearch_isSome_iff_goldbach
      (SigmaExponentImage.exponent x.arithmetic)).trans
      ((halfSigmaImageGoldbachComplete_iff_exponentGoldbach
        x.arithmetic).symm.trans himage.symm)

/-- THEOREM 2: any concrete admissible prime-shadow bridge transfers direct
search success to H1 no-obstruction, and conversely. -/
theorem admissibleDirectSearch_iff_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (B : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    (goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic)).isSome =
        true ↔
      H1SpectralNoObstructionComplete x.spectral := by
  exact (admissibleDirectSearch_iff_rateGoldbach x).trans
    (B.rateGoldbach_iff_h1_no_obstruction x)

/-- THEOREM 3: the coefficient face of P338 transfers to H1 no-obstruction
under the same admissible bridge. -/
theorem admissibleCoefficientPos_iff_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (B : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    0 < goldbachConvolutionCoefficient
        (SigmaExponentImage.exponent x.arithmetic) ↔
      H1SpectralNoObstructionComplete x.spectral := by
  exact
    (goldbachDirectSearch_isSome_iff_coefficient_pos
      (SigmaExponentImage.exponent x.arithmetic)).symm.trans
      (admissibleDirectSearch_iff_h1_no_obstruction B x)

/-- THEOREM 4: if the direct search returns a concrete pair on an admissible
state, that pair is sound and the bridge certifies H1 no-obstruction. -/
theorem admissibleDirectSearch_pair_sound_and_h1
    {P : EulerPrimeCouplingProducers}
    (B : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet)
    {pair : ℕ × ℕ}
    (h :
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
        some pair) :
    GoldbachPairPredicate (SigmaExponentImage.exponent x.arithmetic) pair ∧
      H1SpectralNoObstructionComplete x.spectral := by
  constructor
  · exact goldbachDirectSearch_sound h
  · have hs :
        (goldbachDirectSearch
            (SigmaExponentImage.exponent x.arithmetic)).isSome = true := by
      simp [h]
    exact (admissibleDirectSearch_iff_h1_no_obstruction B x).mp hs

/-- THEOREM 5: the returned pair also has the canonical one-dimensional
search shape `(p, n-p)` on the admissible exponent. -/
theorem admissibleDirectSearch_pair_shape_and_h1
    {P : EulerPrimeCouplingProducers}
    (B : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet)
    {pair : ℕ × ℕ}
    (h :
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
        some pair) :
    pair.1 ≤ SigmaExponentImage.exponent x.arithmetic ∧
      pair.2 = SigmaExponentImage.exponent x.arithmetic - pair.1 ∧
      Nat.Prime pair.1 ∧ Nat.Prime pair.2 ∧
      H1SpectralNoObstructionComplete x.spectral := by
  have hshape := goldbachDirectSearch_shape h
  have hh1 :
      H1SpectralNoObstructionComplete x.spectral :=
    (admissibleDirectSearch_pair_sound_and_h1 B x h).2
  exact ⟨hshape.1, hshape.2.1, hshape.2.2.1, hshape.2.2.2, hh1⟩

/-! ## Certificate -/

/-- A compact certificate for transferring P338's direct finite computation
surface through P325's concrete admissible bridge. -/
structure P339DirectSearchAdmissibleBridgeCertificate : Prop where
  direct_search_iff_rate_goldbach :
    ∀ x : ArithmeticAdmissibleSevenFacet,
      (goldbachDirectSearch
          (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
        HalfSigmaRateGoldbachComplete x.val.rate
  direct_search_iff_h1_no_obstruction :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
      (x : ArithmeticAdmissibleSevenFacet),
      (goldbachDirectSearch
          (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
        H1SpectralNoObstructionComplete x.spectral
  coefficient_pos_iff_h1_no_obstruction :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
      (x : ArithmeticAdmissibleSevenFacet),
      0 < goldbachConvolutionCoefficient
          (SigmaExponentImage.exponent x.arithmetic) ↔
        H1SpectralNoObstructionComplete x.spectral
  returned_pair_sound_and_h1 :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
      (x : ArithmeticAdmissibleSevenFacet)
      {pair : ℕ × ℕ},
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
          some pair ->
        GoldbachPairPredicate
            (SigmaExponentImage.exponent x.arithmetic) pair ∧
          H1SpectralNoObstructionComplete x.spectral
  returned_pair_shape_and_h1 :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
      (x : ArithmeticAdmissibleSevenFacet)
      {pair : ℕ × ℕ},
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
          some pair ->
        pair.1 ≤ SigmaExponentImage.exponent x.arithmetic ∧
          pair.2 = SigmaExponentImage.exponent x.arithmetic - pair.1 ∧
          Nat.Prime pair.1 ∧ Nat.Prime pair.2 ∧
          H1SpectralNoObstructionComplete x.spectral

/-- THEOREM 6: the canonical P339 direct-search/admissible-bridge transfer
certificate. -/
theorem p339DirectSearchAdmissibleBridgeCertificate :
    P339DirectSearchAdmissibleBridgeCertificate where
  direct_search_iff_rate_goldbach :=
    admissibleDirectSearch_iff_rateGoldbach
  direct_search_iff_h1_no_obstruction := by
    intro P B x
    exact admissibleDirectSearch_iff_h1_no_obstruction B x
  coefficient_pos_iff_h1_no_obstruction := by
    intro P B x
    exact admissibleCoefficientPos_iff_h1_no_obstruction B x
  returned_pair_sound_and_h1 := by
    intro P B x pair h
    exact admissibleDirectSearch_pair_sound_and_h1 B x h
  returned_pair_shape_and_h1 := by
    intro P B x pair h
    exact admissibleDirectSearch_pair_shape_and_h1 B x h

end AffineRelaxation
end SaturationMonoid
