import H0mework.Realization.Relations.P651
import H0mework.Physics.JointSources.P662

/-!
# Proposition 664: refined central root with the finite three-nail closure

P662 is the current central projection certificate for
`information = mathematics = matter = energy`.

P651 is the current refined unified-equation root: it carries the corrected
prime-shadow mathematics front door and the P650 finite Standard-Model
three-nail closure.  In particular, it exposes that the current formal
Poincare-resolution `alpha_s` object is the canonical SU7 finite producer, and
it carries the exact inverse residual, the nine Yukawa depths, and the CKM
depth sum.

This file welds those two roots.  The point is not to add another empirical
claim.  It is to make the central grand-unification receipt cite the strongest
currently proved finite producer layer, instead of stopping at the older
input-level surface.

Boundary: this still does not prove smooth SU7-breaking dynamics, threshold /
three-loop RG / Higgs-extra-spectrum dynamics, a full CKM matrix, or a
low-energy fidelity theorem.  It does prove that those remaining debts are now
outside the finite central root, not hidden inside the formula bookkeeping.
-/

noncomputable section

namespace SaturationMonoid

universe u

namespace GrandUnification

open StandardModelConstraint
open StandardModelConstraint.InformationMatterProjection

/-- The refined central root.

It combines the P662 central projection certificate with the P651 refined
unified-equation root.  Downstream files can cite this one object when they
need the current strongest Lean form of the slogan:

* mathematics: P663 / P550--P580 sigma-zero foundation spine;
* information/matter: finite SU7 block-incidence carrier equivalence;
* energy: guarded Hamiltonian / H1 / inverse-branch projection;
* physical finite nails: P650/P651 alpha_s, Yukawa-depth, and CKM closure.
-/
structure RefinedInformationMathMatterEnergyUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  central_projection :
    InformationMathMatterEnergyProjectionCertificate E
  refined_unified_root :
    CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate
  finite_three_nail_closure :
    UnifiedFiniteThreeNailClosureCertificate
  mathematics_foundation_spine :
    Nonempty
      (SigmaZeroMathematicsFoundationCertificate.{0, 0, 0, 0, 0, 0}
        ℝ ℂ Unit)
  alpha_physical_object_canonical :
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
  prime_shadow_supported_sync :
    ∀ (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
      (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
        B.toCommonPredicateProducer),
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral
  no_total_math_front_door :
    Not (Nonempty AffineRelaxation.FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 1: the refined central root is inhabited. -/
def refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    RefinedInformationMathMatterEnergyUnifiedRootCertificate E where
  central_projection :=
    informationMathMatterEnergyProjectionCertificate (E := E)
  refined_unified_root :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
  finite_three_nail_closure :=
    unifiedFiniteThreeNailClosureCertificate
  mathematics_foundation_spine :=
    centralProjection_mathematics_foundation_spine (E := E)
  alpha_physical_object_canonical :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.physical_alpha_object_eq_canonical_su7
  alpha_inverse_residual :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.alpha_inverse_residual
  finite_alpha_inverse_residual :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.finite_alpha_inverse_residual
  yukawa_depths :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.yukawa_depths
  ckm_depth_sum :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.ckm_depth_sum
  prime_shadow_supported_sync :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.prime_shadow_sync
  no_total_math_front_door :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.no_total_math_front_door

/-! ## Focused projections -/

/-- THEOREM 2: the refined central root carries the P663 mathematics spine. -/
theorem refinedCentralRoot_mathematics_foundation_spine
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    Nonempty
      (SigmaZeroMathematicsFoundationCertificate.{0, 0, 0, 0, 0, 0}
        ℝ ℂ Unit) :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).mathematics_foundation_spine

/-- THEOREM 3: the refined central root identifies the current formal
physical alpha object with the canonical SU7 finite producer. -/
theorem refinedCentralRoot_alpha_physical_object_canonical
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).alpha_physical_object_canonical

/-- THEOREM 4: the refined central root exposes the exact physical alpha_s
inverse residual. -/
theorem refinedCentralRoot_alpha_inverse_residual
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511) :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).alpha_inverse_residual

/-- THEOREM 5: the refined central root exposes the exact finite unified-axis
alpha_s inverse residual. -/
theorem refinedCentralRoot_finite_alpha_inverse_residual
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).finite_alpha_inverse_residual

/-- THEOREM 6: the refined central root exposes the nine forced Yukawa
depths. -/
theorem refinedCentralRoot_yukawa_depths
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).yukawa_depths

/-- THEOREM 7: the refined central root exposes the CKM/Jarlskog depth sum on
the whole forced primitive-card / endpoint-ordering surface. -/
theorem refinedCentralRoot_ckm_depth_sum
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).ckm_depth_sum P f T hP hf hT

/-- THEOREM 8: the refined central root carries the supported prime-shadow
math front door and not a total unsupported one. -/
theorem refinedCentralRoot_prime_shadow_supported_sync
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
    (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
      B.toCommonPredicateProducer) :
    AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
      AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).prime_shadow_supported_sync B x

/-- THEOREM 9: the refined central root records that the current mathematics
front door is support-indexed; a total spectral code adapter is still blocked.
-/
theorem refinedCentralRoot_no_total_math_front_door
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    Not (Nonempty AffineRelaxation.FullDomainSpectralExponentCodeAdapter) :=
  (refinedInformationMathMatterEnergyUnifiedRootCertificate
    (E := E)).no_total_math_front_door

end GrandUnification
end SaturationMonoid
