import Mathlib.Tactic
import H0mework.Physics.MixingSources.P603

/-!
# Proposition 604: primitive-card producer for the Yukawa coefficient equations

P603 closed the finite producer-input surface once the coefficient vector
satisfies `YukawaCoefficientCarrierSourceEquations` and the sector schedule
preserves endpoint signatures.  This file lowers the coefficient equations one
more layer: the constants in that vector are generated from named finite
carriers already present in the SU(7) / Poincare / information-matter stack.

The primitive cards are deliberately small:

* low-energy electromagnetic denominator `137`;
* seven-facet information states `128`;
* low-energy visible gauge card `9`;
* unified gauge freedom `48`;
* gauged fundamental block card `5`;
* primitive slogan sector card `3`;
* singlet block card `2`;
* SU(7) block-index card `7`;
* 4D Poincare top-resolution card `4`;
* unit card `1`;
* information/matter component-position card `17`.

Boundary: this is still finite-cardinality production, not a physical
derivation from continuous SU(7)-breaking dynamics or RG flow.  It removes the
remaining local-number debt in the coefficient source equations and feeds the
P603 singleton producer-input theorem.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Primitive finite cards used by the coefficient law -/

/-- The P286 gauged fundamental block card, read as an integer. -/
def gaugedFundamentalBlockCardZ : Int :=
  (Fintype.card GaugedFundamentalBlock : Int)

/-- The P177 primitive slogan-sector card, read as an integer. -/
def primitiveSloganSectorCardZ : Int :=
  (Fintype.card PrimitiveSloganSector : Int)

/-- The P286 gauge-transparent singlet-block card, read as an integer. -/
def gaugeSingletBlockCardZ : Int :=
  (Fintype.card GaugeSingletBlock : Int)

/-- The P286 `3+2+1+1` SU(7) block-index card, read as an integer. -/
def su7FundamentalBlockIndexCardZ : Int :=
  (Fintype.card GaugeProjection.ConcreteBlockDiagonal.SMBlockIndex : Int)

/-- The finite four-dimensional Poincare top-resolution directions. -/
abbrev FourDimensionalPoincareTopResolutionDirection :=
  Fin 4

/-- The 4D Poincare top-resolution card, read as an integer. -/
def fourDimensionalPoincareTopResolutionCardZ : Int :=
  (Fintype.card FourDimensionalPoincareTopResolutionDirection : Int)

/-- A one-point unit card used for affine/unit offsets in the coefficient law.
-/
abbrev YukawaCoefficientUnitCard :=
  Fin 1

/-- The coefficient-law unit card, read as an integer. -/
def yukawaCoefficientUnitCardZ : Int :=
  (Fintype.card YukawaCoefficientUnitCard : Int)

/-- THEOREM 1: primitive card values used by the coefficient law. -/
theorem yukawaCoefficientPrimitiveCards_values :
    gaugedFundamentalBlockCardZ = 5 ∧
      primitiveSloganSectorCardZ = 3 ∧
      gaugeSingletBlockCardZ = 2 ∧
      su7FundamentalBlockIndexCardZ = 7 ∧
      fourDimensionalPoincareTopResolutionCardZ = 4 ∧
      yukawaCoefficientUnitCardZ = 1 ∧
      visibleGaugeCarrierCardFromLowEnergyZ = 9 ∧
      informationMatterSupportCardFromComponentCarrierZ = 17 := by
  norm_num [gaugedFundamentalBlockCardZ, primitiveSloganSectorCardZ,
    gaugeSingletBlockCardZ, su7FundamentalBlockIndexCardZ,
    fourDimensionalPoincareTopResolutionCardZ, yukawaCoefficientUnitCardZ,
    gaugedFundamentalBlock_card_eq_five,
    primitiveSloganSector_card_eq_three, gaugeSingletBlock_card_eq_two,
    smBlockIndex_card_eq_seven,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
    informationMatterSupportCardFromComponentCarrierZ_eq_seventeen]

/-! ## The primitive-card packet and its coefficient vector -/

/-- Primitive finite-card packet for the Yukawa coefficient law. -/
structure YukawaCoefficientPrimitiveCardPacket where
  alphaDenominator : Int
  informationStates : Int
  visibleGauge : Int
  unifiedGaugeFreedom : Int
  gaugedFundamental : Int
  primitiveSectors : Int
  gaugeSinglets : Int
  su7FundamentalBlocks : Int
  poincareTopResolution : Int
  unit : Int
  informationMatterSupport : Int

/-- The canonical primitive-card packet read from existing finite carriers. -/
def canonicalYukawaCoefficientPrimitiveCardPacket :
    YukawaCoefficientPrimitiveCardPacket where
  alphaDenominator := alphaEMIntegerDenominator ℤ
  informationStates := sevenFacetInformationStateCount ℤ
  visibleGauge := visibleGaugeCarrierCardFromLowEnergyZ
  unifiedGaugeFreedom := su7GaugeFreedomDimension ℤ
  gaugedFundamental := gaugedFundamentalBlockCardZ
  primitiveSectors := primitiveSloganSectorCardZ
  gaugeSinglets := gaugeSingletBlockCardZ
  su7FundamentalBlocks := su7FundamentalBlockIndexCardZ
  poincareTopResolution := fourDimensionalPoincareTopResolutionCardZ
  unit := yukawaCoefficientUnitCardZ
  informationMatterSupport := informationMatterSupportCardFromComponentCarrierZ

/-- THEOREM 2: the canonical packet evaluates to the concrete primitive-card
tuple. -/
theorem canonicalYukawaCoefficientPrimitiveCardPacket_values :
    canonicalYukawaCoefficientPrimitiveCardPacket.alphaDenominator = 137 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.informationStates = 128 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.visibleGauge = 9 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.unifiedGaugeFreedom = 48 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.gaugedFundamental = 5 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.primitiveSectors = 3 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.gaugeSinglets = 2 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.su7FundamentalBlocks = 7 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.poincareTopResolution = 4 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.unit = 1 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.informationMatterSupport =
        17 := by
  norm_num [canonicalYukawaCoefficientPrimitiveCardPacket,
    alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension, gaugedFundamentalBlockCardZ,
    primitiveSloganSectorCardZ, gaugeSingletBlockCardZ,
    su7FundamentalBlockIndexCardZ,
    fourDimensionalPoincareTopResolutionCardZ,
    yukawaCoefficientUnitCardZ,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
    informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
    gaugedFundamentalBlock_card_eq_five,
    primitiveSloganSector_card_eq_three, gaugeSingletBlock_card_eq_two,
    smBlockIndex_card_eq_seven]

/-- The Yukawa coefficient vector generated from primitive finite cards. -/
def primitiveCardYukawaDepthStencilCoefficientVector
    (P : YukawaCoefficientPrimitiveCardPacket) :
    YukawaDepthStencilCoefficientVector where
  center :=
    P.gaugedFundamental * P.alphaDenominator -
      P.primitiveSectors
  generationSlope :=
    P.gaugeSinglets * P.alphaDenominator -
      P.su7FundamentalBlocks
  sectorSlope :=
    P.unifiedGaugeFreedom - P.unit
  generationCurvature :=
    -((P.alphaDenominator + P.unit) / P.gaugeSinglets)
  sectorCurvature :=
    -(P.alphaDenominator + P.visibleGauge)
  mixedTwist :=
    -(P.unifiedGaugeFreedom +
      P.gaugeSinglets * P.su7FundamentalBlocks)
  generationCurvatureSector :=
    P.unifiedGaugeFreedom + P.poincareTopResolution
  generationSectorCurvature :=
    (P.visibleGauge + P.unit) ^ (2 : Nat)
  bicurvature :=
    P.informationStates - P.informationMatterSupport

/-- The canonical primitive-card coefficient vector. -/
def canonicalPrimitiveCardYukawaDepthStencilCoefficientVector :
    YukawaDepthStencilCoefficientVector :=
  primitiveCardYukawaDepthStencilCoefficientVector
    canonicalYukawaCoefficientPrimitiveCardPacket

/-- THEOREM 3: primitive finite cards reproduce the P593 carrier-sourced
coefficient vector. -/
theorem canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_eq_carrierSourced :
    canonicalPrimitiveCardYukawaDepthStencilCoefficientVector =
      carrierSourcedYukawaDepthStencilCoefficientVector := by
  ext <;>
    norm_num [canonicalPrimitiveCardYukawaDepthStencilCoefficientVector,
      primitiveCardYukawaDepthStencilCoefficientVector,
      canonicalYukawaCoefficientPrimitiveCardPacket,
      carrierSourcedYukawaDepthStencilCoefficientVector,
      alphaEMIntegerDenominator, sevenFacetInformationStateCount,
      su7GaugeFreedomDimension, gaugedFundamentalBlockCardZ,
      primitiveSloganSectorCardZ, gaugeSingletBlockCardZ,
      su7FundamentalBlockIndexCardZ,
      fourDimensionalPoincareTopResolutionCardZ,
      yukawaCoefficientUnitCardZ,
      visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
      informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
      gaugedFundamentalBlock_card_eq_five,
      primitiveSloganSector_card_eq_three, gaugeSingletBlock_card_eq_two,
      smBlockIndex_card_eq_seven]

/-- THEOREM 4: the primitive-card coefficient vector satisfies P594's
carrier-source equations. -/
theorem canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations :
    YukawaCoefficientCarrierSourceEquations
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector := by
  rw [canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_eq_carrierSourced]
  exact carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations

/-! ## Feeding the P603 producer-input surface -/

/-- The P603 producer input generated by primitive finite cards. -/
def primitiveCardYukawaProducerInputCandidate :
    YukawaProducerInputCandidate where
  coefficients := canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
  schedule := yukawaSectorInformationIncidence

/-- THEOREM 5: the primitive-card producer input is accepted by the P603
surface. -/
theorem primitiveCardYukawaProducerInputCandidate_surface :
    YukawaProducerInputSurface
      primitiveCardYukawaProducerInputCandidate := by
  exact
    ⟨canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations,
      yukawaSectorInformationIncidence_endpointPreserving⟩

/-- THEOREM 6: P603 collapses the primitive-card input to the selected
producer input. -/
theorem primitiveCardYukawaProducerInputCandidate_eq_selected :
    primitiveCardYukawaProducerInputCandidate =
      selectedYukawaProducerInputCandidate :=
  eq_selectedYukawaProducerInputCandidate_of_surface
    primitiveCardYukawaProducerInputCandidate
    primitiveCardYukawaProducerInputCandidate_surface

/-- THEOREM 7: primitive cards generate the documented nine Yukawa depths. -/
theorem primitiveCardYukawaProducerInputCandidate_massOrder_eq :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  yukawaProducerInput_massOrder_eq
    primitiveCardYukawaProducerInputCandidate
    primitiveCardYukawaProducerInputCandidate_surface

/-- THEOREM 8: primitive cards generate CKM/Jarlskog depth sum `386`. -/
theorem primitiveCardYukawaProducerInputCandidate_ckmDepthSum_eq_386 :
    ckmDepthSum_fromYukawaDepthTable
      primitiveCardYukawaProducerInputCandidate.depthTable =
        (ckmCPDepthSum : Int) :=
  yukawaProducerInput_ckmDepthSum_eq_386
    primitiveCardYukawaProducerInputCandidate
    primitiveCardYukawaProducerInputCandidate_surface

/-! ## Bundled receipt -/

/-- Compact receipt: existing finite carriers generate the Yukawa coefficient
source equations, and via P603 they generate the unique nine-depth table and
CKM depth sum `386`.
-/
structure YukawaPrimitiveCardProducerReceipt where
  primitive_card_values :
    gaugedFundamentalBlockCardZ = 5 ∧
      primitiveSloganSectorCardZ = 3 ∧
      gaugeSingletBlockCardZ = 2 ∧
      su7FundamentalBlockIndexCardZ = 7 ∧
      fourDimensionalPoincareTopResolutionCardZ = 4 ∧
      yukawaCoefficientUnitCardZ = 1 ∧
      visibleGaugeCarrierCardFromLowEnergyZ = 9 ∧
      informationMatterSupportCardFromComponentCarrierZ = 17
  packet_values :
    canonicalYukawaCoefficientPrimitiveCardPacket.alphaDenominator = 137 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.informationStates = 128 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.visibleGauge = 9 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.unifiedGaugeFreedom = 48 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.gaugedFundamental = 5 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.primitiveSectors = 3 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.gaugeSinglets = 2 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.su7FundamentalBlocks = 7 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.poincareTopResolution = 4 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.unit = 1 ∧
      canonicalYukawaCoefficientPrimitiveCardPacket.informationMatterSupport =
        17
  coefficient_vector :
    canonicalPrimitiveCardYukawaDepthStencilCoefficientVector =
      carrierSourcedYukawaDepthStencilCoefficientVector
  source_equations :
    YukawaCoefficientCarrierSourceEquations
      canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
  producer_input_surface :
    YukawaProducerInputSurface
      primitiveCardYukawaProducerInputCandidate
  producer_input_unique :
    primitiveCardYukawaProducerInputCandidate =
      selectedYukawaProducerInputCandidate
  mass_order :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ckmDepthSum_fromYukawaDepthTable
      primitiveCardYukawaProducerInputCandidate.depthTable =
        (ckmCPDepthSum : Int)

/-- THEOREM 9: primitive-card producer receipt for Yukawa depths and CKM. -/
theorem yukawaPrimitiveCardProducerReceipt :
    YukawaPrimitiveCardProducerReceipt where
  primitive_card_values := yukawaCoefficientPrimitiveCards_values
  packet_values := canonicalYukawaCoefficientPrimitiveCardPacket_values
  coefficient_vector :=
    canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_eq_carrierSourced
  source_equations :=
    canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_sourceEquations
  producer_input_surface :=
    primitiveCardYukawaProducerInputCandidate_surface
  producer_input_unique :=
    primitiveCardYukawaProducerInputCandidate_eq_selected
  mass_order :=
    primitiveCardYukawaProducerInputCandidate_massOrder_eq
  ckm_depth_sum :=
    primitiveCardYukawaProducerInputCandidate_ckmDepthSum_eq_386

end StandardModelConstraint
end SaturationMonoid
