import Mathlib.Tactic
import H0mework.Physics.JointSources.P371
import H0mework.Physics.RepresentationSources.P511
import H0mework.Physics.YukawaSources.P587

/-!
# Proposition 588: carrier-source coordinates for the Yukawa stencil

P584 wrote the Yukawa depth stencil coefficients using a small list of finite
carrier cards.  P587 then showed that those coefficients are exactly the
finite-difference coordinates of the selected `3 x 3` Yukawa depth grid.

This file lowers the remaining local cards back to their existing carrier
producers:

* the visible gauge card is P371's low-energy gauge carrier `Fin 8 ⊕ Fin 1`;
* the information/matter support card is P511's typed matter/Higgs component
  carrier;
* the selected finite-difference coordinates are the carrier-card expressions
  themselves, not another local lookup table.

Boundary: this is still a finite-cardinality coordinate-source certificate.
It does not yet derive the selected depth grid dynamically from a unique SU(7)
breaking/consolidation order.  It does remove the local `9` and `17` debt from
the coordinate layer by routing them to already proved carrier objects.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Source cards used by the finite-difference coordinates -/

/-- Low-energy visible gauge card, read from P371's explicit finite carrier. -/
def visibleGaugeCarrierCardFromLowEnergyZ : Int :=
  lowEnergyVisibleGaugeDimensionFromCard ℤ

/-- Information/matter support card, read from P511's typed component carrier. -/
def informationMatterSupportCardFromComponentCarrierZ : Int :=
  Fintype.card MatterComponentPosition

/-- THEOREM 1: P584's visible gauge card is the low-energy visible gauge
carrier card from P371. -/
theorem visibleGaugeCarrierCardZ_eq_fromLowEnergyCarrier :
    visibleGaugeCarrierCardZ =
      visibleGaugeCarrierCardFromLowEnergyZ := by
  norm_num [visibleGaugeCarrierCardZ,
    visibleGaugeCarrierCardFromLowEnergyZ, alphaEMIntegerDenominator,
    sevenFacetInformationStateCount,
    lowEnergyVisibleGaugeDimensionFromCard,
    lowEnergyVisibleGaugeCarrier_card_eq_nine]

/-- THEOREM 2: the low-energy visible gauge source card evaluates to `9`. -/
theorem visibleGaugeCarrierCardFromLowEnergyZ_eq_nine :
    visibleGaugeCarrierCardFromLowEnergyZ = 9 := by
  norm_num [visibleGaugeCarrierCardFromLowEnergyZ,
    lowEnergyVisibleGaugeDimensionFromCard,
    lowEnergyVisibleGaugeCarrier_card_eq_nine]

/-- THEOREM 3: P584's information/matter support card is the P511 typed
matter/Higgs component-position carrier card. -/
theorem canonicalInformationMatterSupportCardZ_eq_fromComponentCarrier :
    canonicalInformationMatterSupportCardZ =
      informationMatterSupportCardFromComponentCarrierZ := by
  change (17 : Int) = (Fintype.card MatterComponentPosition : Int)
  exact_mod_cast matterComponentPosition_card.symm

/-- THEOREM 4: the typed information/matter support source card evaluates to
`17`. -/
theorem informationMatterSupportCardFromComponentCarrierZ_eq_seventeen :
    informationMatterSupportCardFromComponentCarrierZ = 17 := by
  change (Fintype.card MatterComponentPosition : Int) = (17 : Int)
  exact_mod_cast matterComponentPosition_card

/-! ## Finite-difference coordinates as carrier-source expressions -/

/-- THEOREM 5: the selected finite-difference coordinates are exactly the
carrier-source expressions from P371/P511/P584. -/
theorem selectedGrid_finiteDifferenceCoordinates_eq_carrierSources :
    (stencilFromGrid selectedYukawaDepthGrid).center =
        (5 * alphaEMIntegerDenominator ℚ - 3) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSlope =
        (2 * alphaEMIntegerDenominator ℚ - 7) ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorSlope =
        (su7GaugeFreedomDimension ℚ - 1) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvature =
        -((alphaEMIntegerDenominator ℚ + 1) / 2) ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature =
        -(alphaEMIntegerDenominator ℚ +
          visibleGaugeCarrierCardFromLowEnergyZ) ∧
      (stencilFromGrid selectedYukawaDepthGrid).mixedTwist =
        -(su7GaugeFreedomDimension ℚ + 2 * (7 : ℚ)) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvatureSector =
        (su7GaugeFreedomDimension ℚ + 4) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSectorCurvature =
        ((visibleGaugeCarrierCardFromLowEnergyZ : ℚ) + 1) ^ (2 : Nat) ∧
      (stencilFromGrid selectedYukawaDepthGrid).bicurvature =
        (sevenFacetInformationStateCount ℚ -
          informationMatterSupportCardFromComponentCarrierZ) := by
  rw [stencilFromGrid_selected_eq_canonical]
  rw [visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
    informationMatterSupportCardFromComponentCarrierZ_eq_seventeen]
  norm_num [RationalYukawaBiquadraticStencil.canonical,
    yukawaDepthStencilCenter, yukawaDepthStencilGenerationSlope,
    yukawaDepthStencilSectorSlope, yukawaDepthStencilGenerationCurvature,
    yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
    yukawaDepthStencilGenerationCurvatureSector,
    yukawaDepthStencilGenerationSectorCurvature,
    yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
    canonicalInformationMatterSupportCardZ,
    alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension]

/-- THEOREM 6: the selected grid's bicurvature coordinate is the information
state count minus the concrete information/matter support component carrier. -/
theorem selectedGrid_bicurvature_eq_informationMinusMatterCarrier :
    (stencilFromGrid selectedYukawaDepthGrid).bicurvature =
      (sevenFacetInformationStateCount ℚ -
        informationMatterSupportCardFromComponentCarrierZ) := by
  exact selectedGrid_finiteDifferenceCoordinates_eq_carrierSources.2.2.2.2.2.2.2.2

/-- THEOREM 7: the selected grid's sector-curvature coordinate is sourced by
the electromagnetic denominator and the low-energy visible gauge carrier. -/
theorem selectedGrid_sectorCurvature_eq_alphaPlusVisibleGauge :
    (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature =
      -(alphaEMIntegerDenominator ℚ +
        visibleGaugeCarrierCardFromLowEnergyZ) := by
  exact selectedGrid_finiteDifferenceCoordinates_eq_carrierSources.2.2.2.2.1

/-! ## Bundled receipt -/

/-- Compact receipt: the finite-difference coordinate layer is routed to
existing finite carrier producers for the visible gauge and information/matter
support cards. -/
structure YukawaDepthCarrierSourceCoordinateReceipt where
  visible_card_source :
    visibleGaugeCarrierCardZ =
      visibleGaugeCarrierCardFromLowEnergyZ
  visible_card_value :
    visibleGaugeCarrierCardFromLowEnergyZ = 9
  information_matter_card_source :
    canonicalInformationMatterSupportCardZ =
      informationMatterSupportCardFromComponentCarrierZ
  information_matter_card_value :
    informationMatterSupportCardFromComponentCarrierZ = 17
  finite_difference_coordinates :
    (stencilFromGrid selectedYukawaDepthGrid).center =
        (5 * alphaEMIntegerDenominator ℚ - 3) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSlope =
        (2 * alphaEMIntegerDenominator ℚ - 7) ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorSlope =
        (su7GaugeFreedomDimension ℚ - 1) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvature =
        -((alphaEMIntegerDenominator ℚ + 1) / 2) ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature =
        -(alphaEMIntegerDenominator ℚ +
          visibleGaugeCarrierCardFromLowEnergyZ) ∧
      (stencilFromGrid selectedYukawaDepthGrid).mixedTwist =
        -(su7GaugeFreedomDimension ℚ + 2 * (7 : ℚ)) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvatureSector =
        (su7GaugeFreedomDimension ℚ + 4) ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSectorCurvature =
        ((visibleGaugeCarrierCardFromLowEnergyZ : ℚ) + 1) ^ (2 : Nat) ∧
      (stencilFromGrid selectedYukawaDepthGrid).bicurvature =
        (sevenFacetInformationStateCount ℚ -
          informationMatterSupportCardFromComponentCarrierZ)
  bicurvature_source :
    (stencilFromGrid selectedYukawaDepthGrid).bicurvature =
      (sevenFacetInformationStateCount ℚ -
        informationMatterSupportCardFromComponentCarrierZ)
  sector_curvature_source :
    (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature =
      -(alphaEMIntegerDenominator ℚ +
        visibleGaugeCarrierCardFromLowEnergyZ)

/-- THEOREM 8: coordinate-source receipt for the selected Yukawa depth grid. -/
theorem yukawaDepthCarrierSourceCoordinateReceipt :
    YukawaDepthCarrierSourceCoordinateReceipt where
  visible_card_source := visibleGaugeCarrierCardZ_eq_fromLowEnergyCarrier
  visible_card_value := visibleGaugeCarrierCardFromLowEnergyZ_eq_nine
  information_matter_card_source :=
    canonicalInformationMatterSupportCardZ_eq_fromComponentCarrier
  information_matter_card_value :=
    informationMatterSupportCardFromComponentCarrierZ_eq_seventeen
  finite_difference_coordinates :=
    selectedGrid_finiteDifferenceCoordinates_eq_carrierSources
  bicurvature_source :=
    selectedGrid_bicurvature_eq_informationMinusMatterCarrier
  sector_curvature_source :=
    selectedGrid_sectorCurvature_eq_alphaPlusVisibleGauge

end StandardModelConstraint
end SaturationMonoid
