import H0mework.Physics.YukawaSources.P666
import H0mework.Arithmetic.PrimeShadow.P625

/-!
# Proposition 667: coded-descent prime-shadow pressure on the unified root

P666 welds the alpha_s and Yukawa producer-pressure receipts onto the current
central root.  P625 separately proves that the canonical coded-descent
prime-shadow producer discharges the P624 injectivity condition:

* the coded arithmetic shadow is injective;
* coded-descent allowedness is exactly supported prime-shadow liftability;
* the coded admissible domain is equivalent to the supported liftability domain.

This file welds those facts into the central pressure root.  It is deliberately
not a proof of Goldbach, RH, or a total arithmetic/spectral front door.  It
does prove that the mathematics-side prime-shadow front door now has a
concrete coded-descent producer attached to the same root that already carries
the alpha_s residual pressure and the Yukawa leave-one-out contract.
-/

noncomputable section

namespace SaturationMonoid

universe u

namespace GrandUnification

open AffineRelaxation
open StandardModelConstraint

/-- The current unified root strengthened by the concrete coded-descent
prime-shadow producer.

This is the pressure-level receipt that keeps the three main front doors in one
object:

* alpha_s residual producer pressure from P665;
* Yukawa depth / leave-one-out pressure from P666;
* concrete coded-descent prime-shadow liftability from P625.
-/
structure CodedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  yukawa_pressure_root :
    YukawaLeaveOneOutPressureUnifiedRootCertificate E
  coded_descent_core :
    CurrentUnifiedEquationCodedDescentLiftabilityCoreCertificate
  coded_descent_liftability :
    CodedDescentPrimeShadowLiftabilityCertificate
  coded_descent_to_support_indexed :
    coded_descent_liftability.to_support_indexed =
      codedDescentSupportIndexedPrimeShadowProducer
  coded_descent_arithmetic_shadow_injective :
    Function.Injective codedDescentArithmeticShadow
  coded_descent_allowed_iff_liftable :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : ArithmeticAdmissibleSevenFacet),
      CodedDescentAllowed A x ↔
        PrimeShadowSupportedLiftable
          (codedDescentSupportIndexedPrimeShadowProducer A) x
  coded_descent_domain_equiv :
    ∀ A : SpectralExponentCodeAdapter,
      CodedAdmissibleDomain A ≃
        { x : ArithmeticAdmissibleSevenFacet //
            PrimeShadowSupportedLiftable
              (codedDescentSupportIndexedPrimeShadowProducer A) x }
  coded_descent_prime_shadow_sync :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CommonPredicateSupportedCodedDomain
        (codedDescentSupportIndexedPrimeShadowProducer A).toCommonPredicateProducer),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral
  alpha_s_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  finite_yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  finite_ckm_depth_sum :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int)

/-- THEOREM 1: the central pressure root with concrete coded-descent
prime-shadow producer is inhabited. -/
def codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CodedDescentPrimeShadowProducerPressureUnifiedRootCertificate E where
  yukawa_pressure_root :=
    yukawaLeaveOneOutPressureUnifiedRootCertificate (E := E)
  coded_descent_core :=
    currentUnifiedEquationCodedDescentLiftabilityCoreCertificate
  coded_descent_liftability :=
    codedDescentPrimeShadowLiftabilityCertificate
  coded_descent_to_support_indexed := rfl
  coded_descent_arithmetic_shadow_injective :=
    codedDescentArithmeticShadow_injective
  coded_descent_allowed_iff_liftable :=
    codedDescentAllowed_iff_primeShadowSupportedLiftable
  coded_descent_domain_equiv :=
    codedDescentDomainEquivPrimeShadowLiftableDomain
  coded_descent_prime_shadow_sync := by
    intro A x
    exact
      refinedCentralRoot_prime_shadow_supported_sync
        (E := E) (codedDescentSupportIndexedPrimeShadowProducer A) x
  alpha_s_residual :=
    (yukawaLeaveOneOutPressureUnifiedRootCertificate
      (E := E)).alpha_pressure_root.current_physical_alpha_inverse_residual
  finite_yukawa_depths :=
    yukawaPressure_finite_depths (E := E)
  finite_ckm_depth_sum :=
    (yukawaLeaveOneOutPressureUnifiedRootCertificate
      (E := E)).finite_ckm_depth_sum

/-! ## Focused projections -/

/-- THEOREM 2: the concrete coded arithmetic shadow is injective at the
unified pressure root. -/
theorem codedDescentPressure_arithmeticShadow_injective
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    Function.Injective codedDescentArithmeticShadow :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).coded_descent_arithmetic_shadow_injective

/-- THEOREM 3: coded-descent allowedness is exactly supported prime-shadow
liftability at the unified pressure root. -/
theorem codedDescentPressure_allowed_iff_liftable
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) :
    CodedDescentAllowed A x ↔
      PrimeShadowSupportedLiftable
        (codedDescentSupportIndexedPrimeShadowProducer A) x :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).coded_descent_allowed_iff_liftable A x

/-- DEFINITION 4: the coded admissible domain is equivalent to the supported
prime-shadow liftability domain at the unified pressure root. -/
def codedDescentPressure_domain_equiv
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : SpectralExponentCodeAdapter) :
    CodedAdmissibleDomain A ≃
      { x : ArithmeticAdmissibleSevenFacet //
          PrimeShadowSupportedLiftable
            (codedDescentSupportIndexedPrimeShadowProducer A) x } :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).coded_descent_domain_equiv A

/-- THEOREM 5: on the canonical coded-descent producer, the central
prime-shadow synchronization theorem applies directly. -/
theorem codedDescentPressure_prime_shadow_sync
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : SpectralExponentCodeAdapter)
    (x : CommonPredicateSupportedCodedDomain
      (codedDescentSupportIndexedPrimeShadowProducer A).toCommonPredicateProducer) :
    HalfSigmaRateGoldbachComplete x.1.val.rate ↔
      H1SpectralNoObstructionComplete x.1.spectral :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).coded_descent_prime_shadow_sync A x

/-- THEOREM 6: the same root still carries the exact alpha_s inverse residual. -/
theorem codedDescentPressure_alpha_s_residual
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511) :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).alpha_s_residual

/-- THEOREM 7: the same root still carries the finite Yukawa depth list. -/
theorem codedDescentPressure_finite_yukawa_depths
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  (codedDescentPrimeShadowProducerPressureUnifiedRootCertificate
    (E := E)).finite_yukawa_depths

end GrandUnification
end SaturationMonoid
