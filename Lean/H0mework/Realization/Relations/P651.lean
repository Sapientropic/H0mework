import H0mework.Arithmetic.PrimeShadow.P623
import H0mework.Physics.JointSources.P650

/-!
# Proposition 651: current unified root with refined three-nail closure

P620-P623 give the current unified-equation root with the corrected
support-indexed Euler prime-shadow mathematical front door.  P650 is newer:
it packages the refined finite Standard-Model three-nail closure
(`alpha_s`, Yukawa depths, CKM/Jarlskog `386`) as one certificate.

This file fuses those two current roots.  It does not add another physics or
number-theory producer.  It proves that the current unified root can now be
read with the refined P650 three-nail certificate, and that the formal
Poincare-resolution `alpha_s` producer is object-equal to the finite
QCD/Poincare unified-axis producer, hence to the canonical SU7-only finite
producer.

Boundary: the remaining open producers are unchanged: smooth SU7 breaking,
threshold / three-loop RG / Higgs-extra dynamics, full CKM matrix, low-energy
fidelity, and the concrete Euler/physics prime-shadow support.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint
open StandardModelConstraint.InformationMatterProjection

/-! ## Physical alpha object identity -/

/-- THEOREM 1: the current formal Poincare-resolution physical `alpha_s`
producer is exactly the finite QCD/Poincare unified-axis producer. -/
theorem currentFormalAlphaStrongPhysical_eq_unifiedAxis :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer :=
  unifiedFiniteThreeNailClosureCertificate.alpha_s_finite.physical_eq_unified_axis
    currentFormalFourDPoincareCertificate
    unifiedGaugeIntoAlphaEMStructural

/-- THEOREM 2: the current formal Poincare-resolution physical `alpha_s`
producer is the canonical SU7-breaking finite residual producer. -/
theorem currentFormalAlphaStrongPhysical_eq_canonicalSU7 :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer := by
  rw [currentFormalAlphaStrongPhysical_eq_unifiedAxis]
  exact
    unifiedFiniteThreeNailClosureCertificate
      |>.alpha_s_finite
      |>.unified_axis_eq_canonical

/-! ## Refined current unified root -/

/-- Current unified-equation root with the corrected prime-shadow math front
door and the refined P650 finite three-nail closure. -/
structure CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate where
  prime_shadow_math_core :
    CurrentUnifiedEquationPrimeShadowMathCoreCertificate
  refined_three_nail_closure :
    UnifiedFiniteThreeNailClosureCertificate
  finite_projection_core :
    FinitePhysicsMathematicsUnificationProjectionCoreCertificate
  formula_coordinate_core :
    CurrentUnifiedEquationFiniteCoreCertificate
  physical_alpha_object_eq_unified_axis :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  physical_alpha_object_eq_canonical_su7 :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  finite_alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)
  prime_shadow_sync :
    ∀ (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
      (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
        B.toCommonPredicateProducer),
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral
  no_total_math_front_door :
    Not (Nonempty AffineRelaxation.FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 3: the current refined unified root is inhabited. -/
def currentUnifiedEquationPrimeShadowThreeNailRootCertificate :
    CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate where
  prime_shadow_math_core := currentUnifiedEquationPrimeShadowMathCoreCertificate
  refined_three_nail_closure := unifiedFiniteThreeNailClosureCertificate
  finite_projection_core := finitePhysicsMathematicsUnificationProjectionCoreCertificate
  formula_coordinate_core := currentUnifiedEquationFiniteCoreCertificate
  physical_alpha_object_eq_unified_axis :=
    currentFormalAlphaStrongPhysical_eq_unifiedAxis
  physical_alpha_object_eq_canonical_su7 :=
    currentFormalAlphaStrongPhysical_eq_canonicalSU7
  alpha_inverse_residual :=
    CurrentUnifiedEquationPrimeShadowMathCoreCertificate.alpha_s_residual
      currentUnifiedEquationPrimeShadowMathCoreCertificate
  finite_alpha_inverse_residual :=
    unifiedFiniteThreeNailClosureCertificate.finite_alpha_inverse_residual
  yukawa_depths := unifiedFiniteThreeNailClosureCertificate.yukawa_depths
  ckm_depth_sum :=
    unifiedFiniteThreeNailClosureCertificate.ckm_depth_sum_on_forced_surface
  prime_shadow_sync :=
    currentUnifiedEquationPrimeShadowMathCoreCertificate.prime_shadow_sync
  no_total_math_front_door :=
    AffineRelaxation.primeShadowSupportedMathFrontDoorCertificate.no_total_math_front_door

namespace CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate

/-- THEOREM 4: the refined root exposes the current physical alpha object as
the canonical SU7 finite producer. -/
theorem alpha_object_canonical
    (C : CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate) :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer :=
  C.physical_alpha_object_eq_canonical_su7

/-- THEOREM 5: the refined root exposes the support-indexed prime-shadow math
sync, not a total spectral code. -/
theorem prime_shadow_supported_sync
    (C : CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate)
    (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
    (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
      B.toCommonPredicateProducer) :
    AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
      AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral :=
  C.prime_shadow_sync B x

end CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate

end SaturationMonoid
