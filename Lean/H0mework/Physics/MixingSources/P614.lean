import H0mework.Physics.MixingSources.P612

/-!
# Proposition 614: CKM depth sum as a sector-coefficient gap

P612 proves that the Jarlskog four-product depth sum cancels to
`2 * (n_s - n_c)` for any Yukawa depth table.  This file lowers the selected
finite stencil one more step:

* `strange` and `charm` live in the same middle-generation row of the P584
  centered stencil;
* their depth gap is therefore the sector-axis coefficient gap
  `sectorSlope - sectorCurvature = 47 - (-146) = 193`;
* the CKM/Jarlskog depth sum is twice that gap, hence `386`.

Boundary: this still does not derive the stencil coefficients from continuous
SU(7) breaking / consolidation dynamics.  It does remove another presentation
layer from the CKM nail: the phase depth sum is controlled by a two-coefficient
sector-axis gap, not by four independent depth deltas.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Strange/charm gap from the finite stencil -/

/-- THEOREM 1: in the selected finite stencil, the strange/charm depth gap is
the sector-axis coefficient gap `sectorSlope - sectorCurvature`. -/
theorem yukawaStencil_strange_minus_charm_eq_sectorSlope_minus_sectorCurvature :
    yukawaDepthStencilOf .strange - yukawaDepthStencilOf .charm =
      yukawaDepthStencilSectorSlope - yukawaDepthStencilSectorCurvature := by
  norm_num [yukawaDepthStencilOf, yukawaDepthStencilAt,
    yukawaMatrixCoordinates, yukawaGenerationDepthCoordinate,
    yukawaSectorDepthCoordinate, yukawaDepthStencilCenter,
    yukawaDepthStencilGenerationSlope, yukawaDepthStencilSectorSlope,
    yukawaDepthStencilGenerationCurvature,
    yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
    yukawaDepthStencilGenerationCurvatureSector,
    yukawaDepthStencilGenerationSectorCurvature,
    yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
    alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension, canonicalInformationMatterSupportCardZ]

/-- THEOREM 2: the sector-axis coefficient gap is `193`. -/
theorem yukawaStencil_sectorSlope_minus_sectorCurvature_eq_193 :
    yukawaDepthStencilSectorSlope - yukawaDepthStencilSectorCurvature =
      (193 : Int) := by
  norm_num [yukawaDepthStencilSectorSlope,
    yukawaDepthStencilSectorCurvature, alphaEMIntegerDenominator,
    su7GaugeFreedomDimension, visibleGaugeCarrierCardZ,
    sevenFacetInformationStateCount]

/-- THEOREM 3: the selected finite stencil has strange/charm depth gap `193`.
-/
theorem yukawaStencil_strange_minus_charm_eq_193 :
    yukawaDepthStencilOf .strange - yukawaDepthStencilOf .charm =
      (193 : Int) := by
  rw [yukawaStencil_strange_minus_charm_eq_sectorSlope_minus_sectorCurvature,
    yukawaStencil_sectorSlope_minus_sectorCurvature_eq_193]

/-! ## Jarlskog four-product normal form from the sector gap -/

/-- The CKM/Jarlskog four-product depth sum read directly from the P584 finite
stencil. -/
def ckmJarlskogDepthSumFromStencil : Int :=
  (yukawaDepthStencilOf .strange - yukawaDepthStencilOf .up) +
    (yukawaDepthStencilOf .bottom - yukawaDepthStencilOf .charm) +
      (yukawaDepthStencilOf .up - yukawaDepthStencilOf .bottom) +
        (yukawaDepthStencilOf .strange - yukawaDepthStencilOf .charm)

/-- THEOREM 4: on the finite stencil, the Jarlskog four-product depth sum is
twice the sector-axis coefficient gap. -/
theorem ckmJarlskogDepthSumFromStencil_eq_twice_sectorCoefficientGap :
    ckmJarlskogDepthSumFromStencil =
      2 * (yukawaDepthStencilSectorSlope -
        yukawaDepthStencilSectorCurvature) := by
  norm_num [ckmJarlskogDepthSumFromStencil,
    yukawaDepthStencilOf, yukawaDepthStencilAt, yukawaMatrixCoordinates,
    yukawaGenerationDepthCoordinate, yukawaSectorDepthCoordinate,
    yukawaDepthStencilCenter, yukawaDepthStencilGenerationSlope,
    yukawaDepthStencilSectorSlope, yukawaDepthStencilGenerationCurvature,
    yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
    yukawaDepthStencilGenerationCurvatureSector,
    yukawaDepthStencilGenerationSectorCurvature,
    yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
    alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension, canonicalInformationMatterSupportCardZ]

/-- THEOREM 5: the finite-stencil Jarlskog depth sum is `386`. -/
theorem ckmJarlskogDepthSumFromStencil_eq_386 :
    ckmJarlskogDepthSumFromStencil = (386 : Int) := by
  rw [ckmJarlskogDepthSumFromStencil_eq_twice_sectorCoefficientGap,
    yukawaStencil_sectorSlope_minus_sectorCurvature_eq_193]
  norm_num

/-! ## Carrier-sourced coefficient vector version -/

/-- THEOREM 6: the carrier-sourced coefficient vector has the same
sector-axis gap `193`. -/
theorem carrierSourcedYukawaSectorCoefficientGap_eq_193 :
    carrierSourcedYukawaDepthStencilCoefficientVector.sectorSlope -
        carrierSourcedYukawaDepthStencilCoefficientVector.sectorCurvature =
      (193 : Int) := by
  norm_num [carrierSourcedYukawaDepthStencilCoefficientVector,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
    alphaEMIntegerDenominator, su7GaugeFreedomDimension]

/-- Compact receipt: the CKM/Jarlskog depth sum is twice the carrier-sourced
sector-axis coefficient gap. -/
structure CKMJarlskogSectorGapReceipt where
  strange_charm_gap_as_coefficients :
    yukawaDepthStencilOf .strange - yukawaDepthStencilOf .charm =
      yukawaDepthStencilSectorSlope - yukawaDepthStencilSectorCurvature
  sector_coefficient_gap :
    yukawaDepthStencilSectorSlope - yukawaDepthStencilSectorCurvature =
      (193 : Int)
  jarlskog_depth_sum_normal_form :
    ckmJarlskogDepthSumFromStencil =
      2 * (yukawaDepthStencilSectorSlope -
        yukawaDepthStencilSectorCurvature)
  jarlskog_depth_sum :
    ckmJarlskogDepthSumFromStencil = (386 : Int)
  carrier_sourced_sector_gap :
    carrierSourcedYukawaDepthStencilCoefficientVector.sectorSlope -
        carrierSourcedYukawaDepthStencilCoefficientVector.sectorCurvature =
      (193 : Int)

/-- THEOREM 7: CKM/Jarlskog sector-gap receipt. -/
theorem ckmJarlskogSectorGapReceipt :
    CKMJarlskogSectorGapReceipt where
  strange_charm_gap_as_coefficients :=
    yukawaStencil_strange_minus_charm_eq_sectorSlope_minus_sectorCurvature
  sector_coefficient_gap :=
    yukawaStencil_sectorSlope_minus_sectorCurvature_eq_193
  jarlskog_depth_sum_normal_form :=
    ckmJarlskogDepthSumFromStencil_eq_twice_sectorCoefficientGap
  jarlskog_depth_sum :=
    ckmJarlskogDepthSumFromStencil_eq_386
  carrier_sourced_sector_gap :=
    carrierSourcedYukawaSectorCoefficientGap_eq_193

end StandardModelConstraint
end SaturationMonoid
