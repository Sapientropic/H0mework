import H0mework.Arithmetic.PrimeSearch.P339

/-!
# Proposition 340: admissible bridge falsifiability

P339 showed the positive transfer: once a concrete admissible prime-shadow
bridge exists, direct Goldbach search and coefficient positivity transfer to
H1 no-obstruction.

This file proves the converse boundary that keeps the bridge honest.  A
concrete admissible bridge is falsifiable: any admissible state where the
arithmetic/direct/coefficient face disagrees with the H1 face refutes the
existence of such a bridge.

Boundary: this still does not construct the missing prime-shadow producer.
It says the producer cannot be arbitrary or cosmetic; it must satisfy these
pointwise projection tests on the admissible domain.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Forced alignment -/

/-- THEOREM 1: any concrete admissible bridge forces the three computable
arithmetic surfaces, direct search, coefficient positivity, and H1
no-obstruction, to agree on every admissible state. -/
theorem admissibleBridge_forces_direct_coefficient_h1_alignment
    {P : EulerPrimeCouplingProducers}
    (B : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    ((goldbachDirectSearch
          (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
        0 < goldbachConvolutionCoefficient
          (SigmaExponentImage.exponent x.arithmetic)) ∧
      ((goldbachDirectSearch
          (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
        H1SpectralNoObstructionComplete x.spectral) ∧
      (0 < goldbachConvolutionCoefficient
          (SigmaExponentImage.exponent x.arithmetic) ↔
        H1SpectralNoObstructionComplete x.spectral) := by
  exact ⟨
    goldbachDirectSearch_isSome_iff_coefficient_pos
      (SigmaExponentImage.exponent x.arithmetic),
    admissibleDirectSearch_iff_h1_no_obstruction B x,
    admissibleCoefficientPos_iff_h1_no_obstruction B x⟩

/-! ## Mismatch refutes the bridge -/

/-- THEOREM 2: a raw-rate Goldbach/H1 mismatch at one admissible state refutes
every concrete admissible bridge for the chosen producer. -/
theorem no_admissibleBridge_of_rateGoldbach_h1_mismatch
    {P : EulerPrimeCouplingProducers}
    (x : ArithmeticAdmissibleSevenFacet)
    (hmismatch :
      Not (HalfSigmaRateGoldbachComplete x.val.rate ↔
        H1SpectralNoObstructionComplete x.spectral)) :
    Not
      (Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)) := by
  rintro ⟨B⟩
  exact hmismatch (B.rateGoldbach_iff_h1_no_obstruction x)

/-- THEOREM 3: a direct-search/H1 mismatch at one admissible state refutes
every concrete admissible bridge for the chosen producer. -/
theorem no_admissibleBridge_of_directSearch_h1_mismatch
    {P : EulerPrimeCouplingProducers}
    (x : ArithmeticAdmissibleSevenFacet)
    (hmismatch :
      Not
        ((goldbachDirectSearch
            (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
          H1SpectralNoObstructionComplete x.spectral)) :
    Not
      (Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)) := by
  rintro ⟨B⟩
  exact hmismatch (admissibleDirectSearch_iff_h1_no_obstruction B x)

/-- THEOREM 4: a coefficient/H1 mismatch at one admissible state refutes
every concrete admissible bridge for the chosen producer. -/
theorem no_admissibleBridge_of_coefficient_h1_mismatch
    {P : EulerPrimeCouplingProducers}
    (x : ArithmeticAdmissibleSevenFacet)
    (hmismatch :
      Not
        (0 < goldbachConvolutionCoefficient
            (SigmaExponentImage.exponent x.arithmetic) ↔
          H1SpectralNoObstructionComplete x.spectral)) :
    Not
      (Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)) := by
  rintro ⟨B⟩
  exact hmismatch (admissibleCoefficientPos_iff_h1_no_obstruction B x)

/-- THEOREM 5: if the direct search returns a prime pair but the spectral side
still has an H1 obstruction, no concrete admissible bridge can exist. -/
theorem no_admissibleBridge_of_returnedPair_and_h1_obstruction
    {P : EulerPrimeCouplingProducers}
    (x : ArithmeticAdmissibleSevenFacet)
    {pair : ℕ × ℕ}
    (h :
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
        some pair)
    (hobs : x.spectral.consolidatedH1Obstruction) :
    Not
      (Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)) := by
  rintro ⟨B⟩
  have hh1 :
      H1SpectralNoObstructionComplete x.spectral :=
    (admissibleDirectSearch_pair_sound_and_h1 B x h).2
  exact hh1 hobs

/-- THEOREM 6: if direct search fails but the spectral side is already
no-obstruction, no concrete admissible bridge can exist. -/
theorem no_admissibleBridge_of_directSearch_failure_and_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (x : ArithmeticAdmissibleSevenFacet)
    (hfail :
      (goldbachDirectSearch
        (SigmaExponentImage.exponent x.arithmetic)).isSome = false)
    (hh1 : H1SpectralNoObstructionComplete x.spectral) :
    Not
      (Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)) := by
  rintro ⟨B⟩
  have hsucc :
      (goldbachDirectSearch
        (SigmaExponentImage.exponent x.arithmetic)).isSome = true :=
    (admissibleDirectSearch_iff_h1_no_obstruction B x).mpr hh1
  rw [hfail] at hsucc
  contradiction

/-! ## Certificate -/

/-- A compact certificate that P325's admissible bridge is not a cosmetic
adapter: it is refuted by any pointwise arithmetic/direct/coefficient/H1
projection mismatch. -/
structure P340AdmissibleBridgeFalsifiabilityCertificate : Prop where
  bridge_forces_alignment :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P)
      (x : ArithmeticAdmissibleSevenFacet),
      ((goldbachDirectSearch
            (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
          0 < goldbachConvolutionCoefficient
            (SigmaExponentImage.exponent x.arithmetic)) ∧
        ((goldbachDirectSearch
            (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
          H1SpectralNoObstructionComplete x.spectral) ∧
        (0 < goldbachConvolutionCoefficient
            (SigmaExponentImage.exponent x.arithmetic) ↔
          H1SpectralNoObstructionComplete x.spectral)
  rate_mismatch_refutes_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (x : ArithmeticAdmissibleSevenFacet),
      Not (HalfSigmaRateGoldbachComplete x.val.rate ↔
        H1SpectralNoObstructionComplete x.spectral) ->
        Not
          (Nonempty
            (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P))
  direct_mismatch_refutes_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (x : ArithmeticAdmissibleSevenFacet),
      Not
        ((goldbachDirectSearch
            (SigmaExponentImage.exponent x.arithmetic)).isSome = true ↔
          H1SpectralNoObstructionComplete x.spectral) ->
        Not
          (Nonempty
            (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P))
  coefficient_mismatch_refutes_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (x : ArithmeticAdmissibleSevenFacet),
      Not
        (0 < goldbachConvolutionCoefficient
            (SigmaExponentImage.exponent x.arithmetic) ↔
          H1SpectralNoObstructionComplete x.spectral) ->
        Not
          (Nonempty
            (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P))
  returned_pair_obstruction_refutes_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (x : ArithmeticAdmissibleSevenFacet)
      {pair : ℕ × ℕ},
      goldbachDirectSearch (SigmaExponentImage.exponent x.arithmetic) =
          some pair ->
        x.spectral.consolidatedH1Obstruction ->
          Not
            (Nonempty
              (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P))
  direct_failure_no_obstruction_refutes_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (x : ArithmeticAdmissibleSevenFacet),
      (goldbachDirectSearch
          (SigmaExponentImage.exponent x.arithmetic)).isSome = false ->
        H1SpectralNoObstructionComplete x.spectral ->
          Not
            (Nonempty
              (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P))

/-- THEOREM 7: the canonical P340 falsifiability certificate. -/
theorem p340AdmissibleBridgeFalsifiabilityCertificate :
    P340AdmissibleBridgeFalsifiabilityCertificate where
  bridge_forces_alignment := by
    intro P B x
    exact admissibleBridge_forces_direct_coefficient_h1_alignment B x
  rate_mismatch_refutes_bridge := by
    intro P x hmismatch
    exact no_admissibleBridge_of_rateGoldbach_h1_mismatch x hmismatch
  direct_mismatch_refutes_bridge := by
    intro P x hmismatch
    exact no_admissibleBridge_of_directSearch_h1_mismatch x hmismatch
  coefficient_mismatch_refutes_bridge := by
    intro P x hmismatch
    exact no_admissibleBridge_of_coefficient_h1_mismatch x hmismatch
  returned_pair_obstruction_refutes_bridge := by
    intro P x pair h hobs
    exact no_admissibleBridge_of_returnedPair_and_h1_obstruction x h hobs
  direct_failure_no_obstruction_refutes_bridge := by
    intro P x hfail hh1
    exact
      no_admissibleBridge_of_directSearch_failure_and_h1_no_obstruction
        x hfail hh1

end AffineRelaxation
end SaturationMonoid
