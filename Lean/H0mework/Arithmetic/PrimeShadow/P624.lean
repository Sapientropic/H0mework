import H0mework.Arithmetic.PrimeShadow.P623

/-!
# Proposition 624: prime-shadow domain equals pullback liftability

P623 lowers the mathematical front door to a support-indexed Euler
prime-shadow producer.  This file proves that the front door is not a side
channel: every supported coded point it accepts actually lifts into the P324
Euler pullback carrier.

It also proves the converse under the precise extra condition needed for it:
the arithmetic shadow map must be injective on the half-sigma arithmetic image.
With that condition, the supported coded domain is exactly the supported
pullback-liftable domain.

Boundary: this still does not construct the final Euler/RH support.  It proves
that any future support cannot merely satisfy the result predicates; it must be
the same thing as liftability into the Euler-coupled pullback carrier, up to
the explicitly named arithmetic-shadow injectivity condition.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Supported pullback liftability -/

/-- A seven-facet point is supported-prime-shadow-liftable when its spectral
projection is in the producer support and its arithmetic/spectral shadows
agree, i.e. when it can be lifted to the P324 pullback carrier with a support
witness. -/
def PrimeShadowSupportedLiftable
    (B : SupportIndexedPrimeShadowProducer)
    (x : ArithmeticAdmissibleSevenFacet) : Prop :=
  ∃ _hs : B.support x.spectral,
    B.producer.arithmeticShadow x.arithmetic =
      B.producer.spectralShadow x.spectral

/-- THEOREM 1: supported liftability is equivalently a supported witness plus
an actual point of the P324 Euler pullback carrier with the same projections.
-/
theorem primeShadowSupportedLiftable_iff_carrier
    (B : SupportIndexedPrimeShadowProducer)
    (x : ArithmeticAdmissibleSevenFacet) :
    PrimeShadowSupportedLiftable B x ↔
      ∃ _hs : B.support x.spectral,
        ∃ z : B.producer.Carrier,
          EulerPrimeCouplingProducers.Carrier.arithmetic z = x.arithmetic ∧
            EulerPrimeCouplingProducers.Carrier.spectral z = x.spectral := by
  constructor
  · rintro ⟨hs, hshadow⟩
    refine ⟨hs, ?_⟩
    exact
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := B.producer) x.arithmetic x.spectral).mpr hshadow
  · rintro ⟨hs, z, harith, hspectral⟩
    refine ⟨hs, ?_⟩
    exact
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := B.producer) x.arithmetic x.spectral).mp
        ⟨z, harith, hspectral⟩

/-! ## P623 accepted domain always lifts -/

/-- THEOREM 2: every point accepted by P623's supported coded domain genuinely
lifts into the P324 Euler pullback carrier. -/
theorem commonPredicateSupportedCodedDomain_subset_primeShadowLiftable
    (B : SupportIndexedPrimeShadowProducer)
    (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer) :
    PrimeShadowSupportedLiftable B x.1 := by
  rcases x.2 with ⟨hs, hcode⟩
  change B.support x.1.spectral at hs
  change
    SigmaExponentImage.exponent x.1.arithmetic =
      B.code x.1.spectral hs at hcode
  have hpoint :
      SigmaExponentImage.ofNat (1 / 2 : ℝ) (B.code x.1.spectral hs) =
        x.1.arithmetic := by
    rw [← hcode]
    exact SigmaExponentImage.ofNat_exponent_eq x.1.arithmetic
  refine ⟨hs, ?_⟩
  calc
    B.producer.arithmeticShadow x.1.arithmetic =
        B.producer.arithmeticShadow
          (SigmaExponentImage.ofNat (1 / 2 : ℝ)
            (B.code x.1.spectral hs)) := by rw [hpoint]
    _ = B.producer.spectralShadow x.1.spectral :=
        (B.supported_shadow_code x.1.spectral hs).symm

/-- THEOREM 3: the same fact in carrier-existence form. -/
theorem commonPredicateSupportedCodedDomain_lifts_to_carrier
    (B : SupportIndexedPrimeShadowProducer)
    (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer) :
    ∃ _hs : B.support x.1.spectral,
      ∃ z : B.producer.Carrier,
        EulerPrimeCouplingProducers.Carrier.arithmetic z = x.1.arithmetic ∧
          EulerPrimeCouplingProducers.Carrier.spectral z = x.1.spectral :=
  (primeShadowSupportedLiftable_iff_carrier B x.1).mp
    (commonPredicateSupportedCodedDomain_subset_primeShadowLiftable B x)

/-! ## Converse under arithmetic-shadow injectivity -/

/-- THEOREM 4: if the arithmetic shadow is injective, supported pullback
liftability is equivalent to P623's supported coded domain predicate. -/
theorem supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hinj : Function.Injective B.producer.arithmeticShadow)
    (x : ArithmeticAdmissibleSevenFacet) :
    SupportedCodedDescentAllowed
        (B.toCommonPredicateProducer.toSupportedSpectralExponentCodeProducer)
        x ↔
      PrimeShadowSupportedLiftable B x := by
  constructor
  · intro hallowed
    exact
      commonPredicateSupportedCodedDomain_subset_primeShadowLiftable B
        ⟨x, hallowed⟩
  · rintro ⟨hs, hshadow⟩
    refine ⟨hs, ?_⟩
    change
      SigmaExponentImage.exponent x.arithmetic =
        B.code x.spectral hs
    have hpoint :
        x.arithmetic =
          SigmaExponentImage.ofNat (1 / 2 : ℝ) (B.code x.spectral hs) := by
      apply hinj
      calc
        B.producer.arithmeticShadow x.arithmetic =
            B.producer.spectralShadow x.spectral := hshadow
        _ = B.producer.arithmeticShadow
              (SigmaExponentImage.ofNat (1 / 2 : ℝ)
                (B.code x.spectral hs)) :=
            B.supported_shadow_code x.spectral hs
    have hexp := congrArg SigmaExponentImage.exponent hpoint
    simpa [SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2] using hexp

/-- THEOREM 5: with arithmetic-shadow injectivity, the subtype of P623
accepted points is equivalent to the subtype of supported pullback-liftable
points. -/
def supportedCodedDomainEquivPrimeShadowLiftableDomain
    (B : SupportIndexedPrimeShadowProducer)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer ≃
      { x : ArithmeticAdmissibleSevenFacet //
          PrimeShadowSupportedLiftable B x } where
  toFun x :=
    ⟨x.1,
      (supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
        B hinj x.1).mp x.2⟩
  invFun x :=
    ⟨x.1,
      (supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
        B hinj x.1).mpr x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-! ## Packaged liftability certificate -/

/-- Compact certificate tying P623's supported domain to the P324 pullback
carrier. -/
structure PrimeShadowSupportedLiftabilityCertificate where
  liftable :
    SupportIndexedPrimeShadowProducer ->
      ArithmeticAdmissibleSevenFacet -> Prop
  liftable_iff_carrier :
    ∀ (B : SupportIndexedPrimeShadowProducer)
      (x : ArithmeticAdmissibleSevenFacet),
      liftable B x ↔
        ∃ _hs : B.support x.spectral,
          ∃ z : B.producer.Carrier,
            EulerPrimeCouplingProducers.Carrier.arithmetic z = x.arithmetic ∧
              EulerPrimeCouplingProducers.Carrier.spectral z = x.spectral
  accepted_subset_liftable :
    ∀ (B : SupportIndexedPrimeShadowProducer)
      (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer),
      liftable B x.1
  accepted_lifts_to_carrier :
    ∀ (B : SupportIndexedPrimeShadowProducer)
      (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer),
      ∃ _hs : B.support x.1.spectral,
        ∃ z : B.producer.Carrier,
          EulerPrimeCouplingProducers.Carrier.arithmetic z = x.1.arithmetic ∧
            EulerPrimeCouplingProducers.Carrier.spectral z = x.1.spectral
  allowed_iff_liftable_of_injective :
    ∀ (B : SupportIndexedPrimeShadowProducer),
      Function.Injective B.producer.arithmeticShadow ->
        ∀ x : ArithmeticAdmissibleSevenFacet,
          SupportedCodedDescentAllowed
              (B.toCommonPredicateProducer
                |>.toSupportedSpectralExponentCodeProducer)
              x ↔
            liftable B x

/-- THEOREM 6: the prime-shadow supported liftability certificate. -/
def primeShadowSupportedLiftabilityCertificate :
    PrimeShadowSupportedLiftabilityCertificate where
  liftable := PrimeShadowSupportedLiftable
  liftable_iff_carrier := primeShadowSupportedLiftable_iff_carrier
  accepted_subset_liftable :=
    commonPredicateSupportedCodedDomain_subset_primeShadowLiftable
  accepted_lifts_to_carrier :=
    commonPredicateSupportedCodedDomain_lifts_to_carrier
  allowed_iff_liftable_of_injective := by
    intro B hinj x
    exact
      supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
        B hinj x

end AffineRelaxation

/-! ## Connection back to the current unified-equation root -/

/-- The current unified-equation root plus the proof that the P623
prime-shadow front door is a genuine P324 pullback-liftability domain. -/
structure CurrentUnifiedEquationPrimeShadowLiftabilityCoreCertificate where
  prime_shadow_math_core :
    CurrentUnifiedEquationPrimeShadowMathCoreCertificate
  liftability :
    AffineRelaxation.PrimeShadowSupportedLiftabilityCertificate
  accepted_points_lift :
    ∀ (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
      (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
        B.toCommonPredicateProducer),
      ∃ _hs : B.support x.1.spectral,
        ∃ z : B.producer.Carrier,
          AffineRelaxation.EulerPrimeCouplingProducers.Carrier.arithmetic z =
              x.1.arithmetic ∧
            AffineRelaxation.EulerPrimeCouplingProducers.Carrier.spectral z =
              x.1.spectral
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 7: the current unified root with P324 pullback-liftability welded
onto the P623 prime-shadow mathematical front door. -/
def currentUnifiedEquationPrimeShadowLiftabilityCoreCertificate :
    CurrentUnifiedEquationPrimeShadowLiftabilityCoreCertificate where
  prime_shadow_math_core := currentUnifiedEquationPrimeShadowMathCoreCertificate
  liftability := AffineRelaxation.primeShadowSupportedLiftabilityCertificate
  accepted_points_lift :=
    AffineRelaxation.commonPredicateSupportedCodedDomain_lifts_to_carrier
  alpha_s_residual :=
    CurrentUnifiedEquationPrimeShadowMathCoreCertificate.alpha_s_residual
      currentUnifiedEquationPrimeShadowMathCoreCertificate

end SaturationMonoid
