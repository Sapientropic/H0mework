import Mathlib.Tactic
import H0mework.Physics.MixingSources.P656

/-!
# Proposition 657: Yukawa primitive cards from the one-axis producer

P606's primitive-card source equations name eleven finite fields.  P633/P632
show that one primitive axis

`axis = b0_QCD + PoincareSlots_4D = 10`

already drives the finite `alpha_s`, Yukawa, and CKM presentations.  P654/P656
then read the Yukawa and CKM nails from one closed primitive-card stencil.

This file removes one more input layer on the Yukawa side.  We define a
one-axis primitive-card source law:

* `visible = axis - 1`;
* `alphaDenominator = 2^7 + visible`;
* the remaining entries are the named SU(7), Poincare, slogan-sector,
  singlet, unit, and information/matter support carriers.

Lean proves that this one-axis source law implies the P606 primitive-card
source equations, hence forces the same closed stencil, the nine Yukawa depths,
and the CKM/Jarlskog depth sum `386`.

Boundary: this still does not derive the primitive one-axis producer itself
from smooth SU(7)-breaking / threshold / three-loop RG / Higgs dynamics.  It
tightens the finite Yukawa producer input once that primitive axis is supplied.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## One-axis primitive-card source law -/

/-- A one-axis source law for the Yukawa primitive-card packet.

The two electromagnetic/visible fields are read from the primitive axis.  The
remaining fields stay attached to their existing finite carriers. -/
def OneAxisYukawaPrimitiveCardSourceLaw
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket) : Prop :=
  (Y.alphaDenominator : ℚ) =
      sevenFacetInformationStateCount ℚ + (P.axis - 1) ∧
    Y.informationStates = sevenFacetInformationStateCount ℤ ∧
    (Y.visibleGauge : ℚ) = P.axis - 1 ∧
    Y.unifiedGaugeFreedom = su7GaugeFreedomDimension ℤ ∧
    Y.gaugedFundamental = gaugedFundamentalBlockCardZ ∧
    Y.primitiveSectors = primitiveSloganSectorCardZ ∧
    Y.gaugeSinglets = gaugeSingletBlockCardZ ∧
    Y.su7FundamentalBlocks = su7FundamentalBlockIndexCardZ ∧
    Y.poincareTopResolution = fourDimensionalPoincareTopResolutionCardZ ∧
    Y.unit = yukawaCoefficientUnitCardZ ∧
    Y.informationMatterSupport =
      informationMatterSupportCardFromComponentCarrierZ

/-- THEOREM 1: the canonical primitive-card packet satisfies the one-axis
source law for any primitive one-axis producer. -/
theorem canonicalYukawaPrimitiveCardPacket_oneAxisSourceLaw
    (P : OneAxisPrimitiveSourceProducer) :
    OneAxisYukawaPrimitiveCardSourceLaw P
      canonicalYukawaCoefficientPrimitiveCardPacket := by
  have haxis := oneAxisPrimitiveSourceProducer_axis_eq_ten P
  norm_num [OneAxisYukawaPrimitiveCardSourceLaw,
    canonicalYukawaCoefficientPrimitiveCardPacket,
    haxis, alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension, visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]

/-- THEOREM 2: the one-axis source law implies the P606 primitive-card source
equations. -/
theorem oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (hY : OneAxisYukawaPrimitiveCardSourceLaw P Y) :
    YukawaPrimitiveCardSourceEquations Y := by
  rcases hY with
    ⟨hAlphaQ, hInfo, hVisibleQ, hUnified, hGauged, hSectors, hSinglets,
      hBlocks, hPoincare, hUnit, hSupport⟩
  have haxis := oneAxisPrimitiveSourceProducer_axis_eq_ten P
  have hAlphaQ' : (Y.alphaDenominator : ℚ) = (137 : ℚ) := by
    rw [haxis] at hAlphaQ
    norm_num [sevenFacetInformationStateCount] at hAlphaQ
    exact hAlphaQ
  have hVisibleQ' : (Y.visibleGauge : ℚ) = (9 : ℚ) := by
    rw [haxis] at hVisibleQ
    norm_num at hVisibleQ
    exact hVisibleQ
  have hAlpha : Y.alphaDenominator = alphaEMIntegerDenominator ℤ := by
    norm_num [alphaEMIntegerDenominator]
    exact_mod_cast hAlphaQ'
  have hVisible : Y.visibleGauge = visibleGaugeCarrierCardFromLowEnergyZ := by
    rw [visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]
    exact_mod_cast hVisibleQ'
  exact
    ⟨hAlpha, hInfo, hVisible, hUnified, hGauged, hSectors, hSinglets,
      hBlocks, hPoincare, hUnit, hSupport⟩

/-- THEOREM 3: any packet satisfying the one-axis source law is the canonical
primitive-card packet. -/
theorem eq_canonicalYukawaPrimitiveCardPacket_of_oneAxisSourceLaw
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (hY : OneAxisYukawaPrimitiveCardSourceLaw P Y) :
    Y = canonicalYukawaCoefficientPrimitiveCardPacket :=
  eq_canonicalYukawaCoefficientPrimitiveCardPacket_of_sourceEquations Y
    (oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations P Y hY)

/-! ## Depth and CKM consequences -/

/-- THEOREM 4: one-axis primitive-card source data forces the documented
Yukawa depth mass-order list. -/
theorem oneAxisYukawaPrimitiveCardSourceLaw_forces_massOrder
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hY : OneAxisYukawaPrimitiveCardSourceLaw P Y)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector Y) f) :
    T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  yukawaDepthMassOrder_forced_of_primitiveCards_and_endpointSchedule
    Y f T
    (oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations P Y hY)
    hf hT

/-- THEOREM 5: one-axis primitive-card source data forces the typed
Jarlskog depth sum `386`. -/
theorem oneAxisYukawaPrimitiveCardSourceLaw_forces_typedJarlskog
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hY : OneAxisYukawaPrimitiveCardSourceLaw P Y)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector Y) f) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) :=
  yukawaTypedJarlskog_forced_of_primitiveCards_and_endpointSchedule
    Y f T
    (oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations P Y hY)
    hf hT

/-- THEOREM 6: the closed primitive-card stencil table generated from a
one-axis source-law packet forces CKM/Jarlskog depth sum `386`. -/
theorem oneAxisClosedStencilCKMJarlskogDepthSum_eq_386
    (P : OneAxisPrimitiveSourceProducer)
    (Y : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hY : OneAxisYukawaPrimitiveCardSourceLaw P Y)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate Y f) =
      (ckmCPDepthSum : Int) :=
  closedStencilCKMJarlskogFourProductDepthSum_eq_386
    Y f
    (oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations P Y hY)
    hf

/-! ## Certificate -/

/-- Compact certificate: once a primitive one-axis producer is supplied, the
Yukawa primitive-card source equations are no longer eleven independent
fields.  The alpha/visible fields are axis-derived, the rest are named finite
carriers, and the same closed-stencil depth/CKM outputs follow. -/
structure OneAxisYukawaDepthProducerCertificate
    (P : OneAxisPrimitiveSourceProducer) where
  one_axis :
    OneAxisPrimitiveSourceProducerReceipt P
  canonical_one_axis_source :
    OneAxisYukawaPrimitiveCardSourceLaw P
      canonicalYukawaCoefficientPrimitiveCardPacket
  source_law_to_source_equations :
    ∀ Y : YukawaCoefficientPrimitiveCardPacket,
      OneAxisYukawaPrimitiveCardSourceLaw P Y ->
        YukawaPrimitiveCardSourceEquations Y
  source_law_singleton :
    ∀ Y : YukawaCoefficientPrimitiveCardPacket,
      OneAxisYukawaPrimitiveCardSourceLaw P Y ->
        Y = canonicalYukawaCoefficientPrimitiveCardPacket
  closed_stencil :
    CKMJarlskogClosedStencilProducerCertificate
  mass_order :
    ∀ (Y : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        OneAxisYukawaPrimitiveCardSourceLaw P Y ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector Y) f ->
              T.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  typed_jarlskog :
    ∀ (Y : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        OneAxisYukawaPrimitiveCardSourceLaw P Y ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector Y) f ->
              ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)
  closed_stencil_jarlskog :
    ∀ (Y : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        OneAxisYukawaPrimitiveCardSourceLaw P Y ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            ckmJarlskogFourProductDepthSum
                (yukawaPrimitiveCardClosedDepthTableCandidate Y f) =
              (ckmCPDepthSum : Int)

/-- THEOREM 7: one-axis Yukawa-depth producer certificate. -/
theorem oneAxisYukawaDepthProducerCertificate
    (P : OneAxisPrimitiveSourceProducer) :
    OneAxisYukawaDepthProducerCertificate P where
  one_axis := oneAxisPrimitiveSourceProducerReceipt P
  canonical_one_axis_source :=
    canonicalYukawaPrimitiveCardPacket_oneAxisSourceLaw P
  source_law_to_source_equations :=
    oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations P
  source_law_singleton :=
    eq_canonicalYukawaPrimitiveCardPacket_of_oneAxisSourceLaw P
  closed_stencil := ckmJarlskogClosedStencilProducerCertificate
  mass_order := oneAxisYukawaPrimitiveCardSourceLaw_forces_massOrder P
  typed_jarlskog :=
    oneAxisYukawaPrimitiveCardSourceLaw_forces_typedJarlskog P
  closed_stencil_jarlskog :=
    oneAxisClosedStencilCKMJarlskogDepthSum_eq_386 P

/-- THEOREM 8: the canonical primitive one-axis source carries the compressed
Yukawa-depth producer certificate. -/
theorem canonicalOneAxisYukawaDepthProducerCertificate :
    OneAxisYukawaDepthProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer :=
  oneAxisYukawaDepthProducerCertificate
    canonicalOneAxisPrimitiveSourceProducer

end StandardModelConstraint
end SaturationMonoid
