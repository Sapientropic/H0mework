import H0mework.Physics.AlphaSources.P618

/-!
# Proposition 619: finite producer-debt three-nail receipt

The current shortest path has three producer-debt nails:

1. `alpha_s` residual producer;
2. Yukawa depth producer;
3. CKM/Jarlskog depth-sum producer.

The preceding files now close the finite layer of all three:

* P618: finite-geometry physical producer for the exact `alpha_s` inverse
  residual `-89000/128511`;
* P599/P604/P615: primitive-card / generated-table / coefficient-surface
  receipts forcing the nine Yukawa depths
  `[50, 346, 372, 489, 583, 682, 880, 908, 982]`;
* P617: four-card CKM sector-axis producer forcing Jarlskog depth sum `386`.

Boundary: this receipt intentionally stays at the finite producer layer.  It
does not claim the remaining smooth dynamics: threshold spectrum, three-loop
RG, Higgs-extra-representation dynamics, real GUT-scale Yukawa extraction, or
full CKM matrix entries.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- Compact receipt for the three finite producer-debt nails. -/
structure FiniteProducerDebtThreeNailReceipt where
  alpha_s :
    AlphaStrongPhysicalFiniteGeometryProducerReceipt
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural
  yukawa_primitive_cards :
    YukawaPrimitiveCardProducerReceipt
  yukawa_generated_table :
    YukawaDepthTableGeneratedSingletonReceipt
  yukawa_coefficient_no_choice :
    YukawaCarrierCoefficientNoChoiceReceipt
  ckm_sector_axis :
    CKMSectorAxisPrimitiveCardProducerReceipt
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  yukawa_depths_from_primitive_cards :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  yukawa_depths_from_generated_surface :
    ∀ T : YukawaDepthTableCandidate,
      YukawaDepthTableGeneratedSurface T ->
        T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  yukawa_depths_from_coefficient_surface :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ->
        rationalGridMassOrder (gridOfStencil C) =
          [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_jarlskog_depth_sum :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)

/-- THEOREM 1: the finite three-nail producer receipt is inhabited. -/
noncomputable def finiteProducerDebtThreeNailReceipt :
    FiniteProducerDebtThreeNailReceipt where
  alpha_s :=
    alphaStrongPhysicalFiniteGeometryProducerReceipt
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural
  yukawa_primitive_cards := yukawaPrimitiveCardProducerReceipt
  yukawa_generated_table := yukawaDepthTableGeneratedSingletonReceipt
  yukawa_coefficient_no_choice := yukawaCarrierCoefficientNoChoiceReceipt
  ckm_sector_axis := ckmSectorAxisPrimitiveCardProducerReceipt
  alpha_inverse_residual :=
    alphaStrongPhysicalFiniteGeometryProducer_inverseCorrection
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural
  yukawa_depths_from_primitive_cards :=
    primitiveCardYukawaProducerInputCandidate_massOrder_eq
  yukawa_depths_from_generated_surface :=
    yukawaDepthTableGeneratedSurface_massOrder_eq
  yukawa_depths_from_coefficient_surface :=
    rationalStencilCarrierCoefficientSurface_massOrder_eq
  ckm_jarlskog_depth_sum :=
    canonicalCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386

end StandardModelConstraint
end SaturationMonoid
