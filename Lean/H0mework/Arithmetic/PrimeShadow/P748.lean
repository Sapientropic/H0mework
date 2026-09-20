import H0mework.Arithmetic.PrimeShadow.P747

/-!
# Proposition 748: full coded-descent prime realization normal form

P746 defined the full prime-indexed realization gate: every prime exponent
must be realized by a half-sigma arithmetic point and by an H1-spectral point
with the same prime code, inside a structured concrete bridge.

P747 welded the weaker non-tautological three-prime-code gate into the actual
coded-descent representative surface.  This file closes the stronger P746
realization seam for coded descent.

For a spectral exponent adapter `A`, full coded-descent prime realization is
exactly the product of two producer obligations:

* a concrete admissible prime-shadow bridge for the coded-descent producer;
* prime-code range: every prime exponent is hit by some spectral point's code.

Thus the P746 full gate is not a naming layer.  It has a precise normal form:
concrete synchronization content plus prime-index spectral coverage.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Prime-code range for spectral exponent adapters -/

/-- A spectral exponent adapter ranges over the prime exponents when every
prime exponent is the code of some H1-spectral point. -/
def SpectralExponentPrimeCodeSurjective
    (A : SpectralExponentCodeAdapter) : Prop :=
  ∀ p : PrimeExponent,
    ∃ s : H1SpectralProjection (1 / 2 : ℝ), A.code s = p.1

/-- The canonical coded-descent structured bridge obtained from a concrete
admissible bridge by using P543's coded prime-indexed structure. -/
def codedDescentStructuredBridgeOfConcrete
    (A : SpectralExponentCodeAdapter)
    (B :
      ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
        (codedDescentEulerPrimeCouplingProducer A)) :
    StructuredConcreteAdmissiblePrimeShadowBridge
      (codedDescentEulerPrimeCouplingProducer A) where
  concrete := B
  prime_indexed := codedDescentPrimeIndexedShadowStructure A

/-- THEOREM 1: the canonical coded prime code is exactly the arithmetic shadow
of the named half-sigma prime image. -/
theorem codedDescentPrimeCode_eq_halfSigmaPrimeArithmeticShadow
    (A : SpectralExponentCodeAdapter) (p : PrimeExponent) :
    (codedDescentPrimeIndexedShadowStructure A).primeCode p =
      (codedDescentEulerPrimeCouplingProducer A).arithmeticShadow
        (halfSigmaPrimeArithmeticImage p) := by
  rfl

/-! ## Full realization from concrete bridge plus prime-code range -/

/-- THEOREM 2: a concrete coded-descent bridge plus prime-code range produces
the full P746 prime-indexed realization. -/
def codedDescentPrimeIndexedRealizationOfConcreteAndPrimeRange
    (A : SpectralExponentCodeAdapter)
    (B :
      ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
        (codedDescentEulerPrimeCouplingProducer A))
    (hrange : SpectralExponentPrimeCodeSurjective A) :
    PrimeIndexedShadowRealization (codedDescentEulerPrimeCouplingProducer A) where
  structured := codedDescentStructuredBridgeOfConcrete A B
  spectralPrime := fun p => Classical.choose (hrange p)
  arithmetic_prime_shadow := by
    intro p
    exact
      (codedDescentPrimeCode_eq_halfSigmaPrimeArithmeticShadow A p).symm
  spectral_prime_shadow := by
    intro p
    have hcode : A.code (Classical.choose (hrange p)) = p.1 :=
      Classical.choose_spec (hrange p)
    dsimp [codedDescentStructuredBridgeOfConcrete,
      codedDescentPrimeIndexedShadowStructure, codedDescentPrimeCode,
      codedDescentEulerPrimeCouplingProducer, codedDescentSpectralShadow,
      codedDescentArithmeticShadow, halfSigmaPrimeImage,
      halfSigmaPrimeArithmeticImage]
    rw [hcode]
    rw [SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2]
    exact (Quot.sound (CodedDescentShadowRel.glue p.1
      (Classical.choose (hrange p)))).symm

/-- THEOREM 3: any full coded-descent prime-indexed realization forces
prime-code range for the spectral exponent adapter. -/
theorem codedDescentPrimeCodeRange_of_primeIndexedRealization
    (A : SpectralExponentCodeAdapter)
    (R :
      PrimeIndexedShadowRealization
        (codedDescentEulerPrimeCouplingProducer A)) :
    SpectralExponentPrimeCodeSurjective A := by
  intro p
  refine ⟨R.spectralPrime p, ?_⟩
  have hshadow :
      codedDescentSpectralShadow A (R.spectralPrime p) =
        codedDescentArithmeticShadow (halfSigmaPrimeArithmeticImage p) := by
    change
      (codedDescentEulerPrimeCouplingProducer A).spectralShadow
          (R.spectralPrime p) =
        (codedDescentEulerPrimeCouplingProducer A).arithmeticShadow
          (halfSigmaPrimeArithmeticImage p)
    exact (R.spectral_prime_shadow p).trans (R.arithmetic_prime_shadow p).symm
  have hcode := congrArg codedDescentShadowExponent hshadow
  simpa [codedDescentShadowExponent_spectral,
    codedDescentShadowExponent_arithmetic,
    halfSigmaPrimeArithmeticImage_exponent] using hcode

/-- THEOREM 4: the full coded-descent P746 realization gate is exactly
concrete synchronization content plus prime-code spectral range. -/
theorem codedDescentPrimeIndexedRealization_iff_concreteBridge_and_primeRange
    (A : SpectralExponentCodeAdapter) :
    Nonempty
        (PrimeIndexedShadowRealization
          (codedDescentEulerPrimeCouplingProducer A)) ↔
      Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
          (codedDescentEulerPrimeCouplingProducer A)) ∧
        SpectralExponentPrimeCodeSurjective A := by
  constructor
  · rintro ⟨R⟩
    exact ⟨⟨R.structured.concrete⟩,
      codedDescentPrimeCodeRange_of_primeIndexedRealization A R⟩
  · rintro ⟨⟨B⟩, hrange⟩
    exact ⟨codedDescentPrimeIndexedRealizationOfConcreteAndPrimeRange
      A B hrange⟩

/-! ## Packaged certificate -/

/-- P748 packages the full coded-descent P746 realization normal form. -/
structure CodedDescentFullPrimeRealizationNormalFormCertificate where
  p747_surface :
    NonTautologicalCodedDescentHolyGrailCertificate
  prime_range :
    SpectralExponentCodeAdapter -> Prop
  concrete_to_structured :
    ∀ A : SpectralExponentCodeAdapter,
      ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
        (codedDescentEulerPrimeCouplingProducer A) ->
        StructuredConcreteAdmissiblePrimeShadowBridge
          (codedDescentEulerPrimeCouplingProducer A)
  realization_iff_concrete_bridge_and_prime_range :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty
          (PrimeIndexedShadowRealization
            (codedDescentEulerPrimeCouplingProducer A)) ↔
        Nonempty
          (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
            (codedDescentEulerPrimeCouplingProducer A)) ∧
          prime_range A
  realization_implies_prime_range :
    ∀ A : SpectralExponentCodeAdapter,
      PrimeIndexedShadowRealization
          (codedDescentEulerPrimeCouplingProducer A) ->
        prime_range A

/-- DEFINITION 1: canonical P748 full prime-realization normal-form
certificate. -/
def codedDescentFullPrimeRealizationNormalFormCertificate :
    CodedDescentFullPrimeRealizationNormalFormCertificate where
  p747_surface := nonTautologicalCodedDescentHolyGrailCertificate
  prime_range := SpectralExponentPrimeCodeSurjective
  concrete_to_structured := codedDescentStructuredBridgeOfConcrete
  realization_iff_concrete_bridge_and_prime_range :=
    codedDescentPrimeIndexedRealization_iff_concreteBridge_and_primeRange
  realization_implies_prime_range :=
    codedDescentPrimeCodeRange_of_primeIndexedRealization

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P748's full coded-descent prime-realization
normal form welded below P747. -/
structure CodedDescentFullPrimeRealizationUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p747_root :
    NonTautologicalCodedDescentHolyGrailUnifiedRootCertificate E
  full_prime_realization :
    CodedDescentFullPrimeRealizationNormalFormCertificate
  realization_iff_concrete_bridge_and_prime_range :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty
          (PrimeIndexedShadowRealization
            (codedDescentEulerPrimeCouplingProducer A)) ↔
        Nonempty
          (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
            (codedDescentEulerPrimeCouplingProducer A)) ∧
          SpectralExponentPrimeCodeSurjective A
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 5: the current central root with P748's full coded-descent
prime-realization normal form. -/
def codedDescentFullPrimeRealizationUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CodedDescentFullPrimeRealizationUnifiedRootCertificate E where
  p747_root :=
    nonTautologicalCodedDescentHolyGrailUnifiedRootCertificate (E := E)
  full_prime_realization :=
    codedDescentFullPrimeRealizationNormalFormCertificate
  realization_iff_concrete_bridge_and_prime_range :=
    codedDescentPrimeIndexedRealization_iff_concreteBridge_and_primeRange
  alpha_s_residual :=
    (nonTautologicalCodedDescentHolyGrailUnifiedRootCertificate
      (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
