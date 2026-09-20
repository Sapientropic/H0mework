import H0mework.Physics.MixingSources.P615

/-!
# Proposition 616: CKM/Jarlskog only needs the sector-axis source equations

P615 proves that the full carrier-sourced Yukawa coefficient vector leaves no
freedom in the nine-depth grid.  The CKM/Jarlskog nail is even sharper: its
typed four-product ignores seven of the nine stencil coefficients.

For any rational biquadratic Yukawa stencil `C`, the Jarlskog depth sum of the
grid it generates is

`2 * (C.sectorSlope - C.sectorCurvature)`.

Thus the CKM depth sum `386` follows from only two carrier equations:

* `sectorSlope = dim SU(7) - 1`;
* `sectorCurvature = -(alphaEM denominator + low-energy visible gauge)`.

Boundary: this still does not derive those two sector-axis equations from
continuous SU(7)-breaking dynamics.  It proves that, for the CKM/Jarlskog
phase, the rest of the Yukawa coefficient vector is irrelevant once this
sector-axis carrier pair is produced.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Sector-axis source equations -/

/-- The minimal carrier-source surface needed for the CKM/Jarlskog depth sum.

This intentionally forgets the other seven Yukawa stencil coefficients.  It is
the smaller producer target for the CKM nail. -/
def RationalStencilSectorAxisSourceEquations
    (C : RationalYukawaBiquadraticStencil) : Prop :=
  C.sectorSlope = su7GaugeFreedomDimension ℚ - 1 ∧
    C.sectorCurvature =
      -(alphaEMIntegerDenominator ℚ +
        (visibleGaugeCarrierCardFromLowEnergyZ : ℚ))

/-- THEOREM 1: the full carrier coefficient surface implies the smaller
sector-axis surface. -/
theorem rationalStencilCarrierCoefficientSurface_to_sectorAxis
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilCarrierCoefficientSurface C) :
    RationalStencilSectorAxisSourceEquations C := by
  rcases hC with
    ⟨_hCenter, _hGenerationSlope, hSectorSlope, _hGenerationCurvature,
      hSectorCurvature, _hMixedTwist, _hGenerationCurvatureSector,
      _hGenerationSectorCurvature, _hBicurvature⟩
  constructor
  · rw [hSectorSlope]
    norm_num [carrierSourcedYukawaDepthStencilCoefficientVector,
      su7GaugeFreedomDimension]
  · rw [hSectorCurvature]
    norm_num [carrierSourcedYukawaDepthStencilCoefficientVector,
      alphaEMIntegerDenominator, visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]

/-- THEOREM 2: the canonical stencil satisfies the minimal sector-axis source
surface. -/
theorem canonical_rationalStencilSectorAxisSourceEquations :
    RationalStencilSectorAxisSourceEquations
      RationalYukawaBiquadraticStencil.canonical := by
  exact rationalStencilCarrierCoefficientSurface_to_sectorAxis
    RationalYukawaBiquadraticStencil.canonical
    canonical_rationalStencilCarrierCoefficientSurface

/-! ## Jarlskog depends only on the sector-axis gap -/

/-- THEOREM 3: for any rational biquadratic stencil, the typed Jarlskog
four-product depth sum of its generated grid is twice the sector-axis
coefficient gap. -/
theorem ckmJarlskogDepthSum_gridOfStencil_eq_twice_sectorAxisGap
    (C : RationalYukawaBiquadraticStencil) :
    ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
      2 * (C.sectorSlope - C.sectorCurvature) := by
  rcases C with
    ⟨center, generationSlope, sectorSlope, generationCurvature,
      sectorCurvature, mixedTwist, generationCurvatureSector,
      generationSectorCurvature, bicurvature⟩
  norm_num [ckmJarlskogDepthSumFromRationalGrid, rationalGridDepthOf,
    gridOfStencil, RationalYukawaBiquadraticStencil.eval,
    yukawaMatrixCoordinates, yukawaGenerationDepthCoordinate,
    yukawaSectorDepthCoordinate]
  ring

/-- THEOREM 4: the sector-axis carrier equations force the CKM/Jarlskog depth
sum `386`. -/
theorem rationalStencilSectorAxisSourceEquations_jarlskogDepthSum_eq_386
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilSectorAxisSourceEquations C) :
    ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
      (386 : ℚ) := by
  rw [ckmJarlskogDepthSum_gridOfStencil_eq_twice_sectorAxisGap C]
  rcases hC with ⟨hSlope, hCurvature⟩
  rw [hSlope, hCurvature]
  norm_num [su7GaugeFreedomDimension, alphaEMIntegerDenominator,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]

/-- THEOREM 5: any rational stencil on the full carrier coefficient surface
has Jarlskog depth sum `386`, already through the smaller sector-axis surface.
-/
theorem rationalStencilCarrierCoefficientSurface_jarlskogDepthSum_eq_386_via_sectorAxis
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilCarrierCoefficientSurface C) :
    ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
      (386 : ℚ) :=
  rationalStencilSectorAxisSourceEquations_jarlskogDepthSum_eq_386 C
    (rationalStencilCarrierCoefficientSurface_to_sectorAxis C hC)

/-! ## The carrier arithmetic of the sector gap -/

/-- The sector-axis carrier gap before multiplying by the Jarlskog factor `2`.
-/
def rationalSectorAxisCarrierGap : ℚ :=
  (su7GaugeFreedomDimension ℚ - 1) -
    (-(alphaEMIntegerDenominator ℚ +
      (visibleGaugeCarrierCardFromLowEnergyZ : ℚ)))

/-- THEOREM 6: the sector-axis carrier gap is exactly `193`. -/
theorem rationalSectorAxisCarrierGap_eq_193 :
    rationalSectorAxisCarrierGap = (193 : ℚ) := by
  norm_num [rationalSectorAxisCarrierGap, su7GaugeFreedomDimension,
    alphaEMIntegerDenominator, visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]

/-- THEOREM 7: twice the sector-axis carrier gap is exactly the CKM/Jarlskog
depth sum `386`. -/
theorem twice_rationalSectorAxisCarrierGap_eq_386 :
    2 * rationalSectorAxisCarrierGap = (386 : ℚ) := by
  rw [rationalSectorAxisCarrierGap_eq_193]
  norm_num

/-! ## Bundled receipt -/

/-- Compact receipt: the CKM/Jarlskog depth producer only needs the sector-axis
carrier pair, not the full Yukawa coefficient vector. -/
structure CKMJarlskogSectorAxisMinimalProducerReceipt where
  full_surface_to_sector_axis :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ->
        RationalStencilSectorAxisSourceEquations C
  canonical_sector_axis :
    RationalStencilSectorAxisSourceEquations
      RationalYukawaBiquadraticStencil.canonical
  jarlskog_normal_form :
    ∀ C : RationalYukawaBiquadraticStencil,
      ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
        2 * (C.sectorSlope - C.sectorCurvature)
  sector_axis_forces_386 :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilSectorAxisSourceEquations C ->
        ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
          (386 : ℚ)
  carrier_gap :
    rationalSectorAxisCarrierGap = (193 : ℚ)
  twice_carrier_gap :
    2 * rationalSectorAxisCarrierGap = (386 : ℚ)

/-- THEOREM 8: minimal sector-axis producer receipt for the CKM/Jarlskog
depth sum. -/
theorem ckmJarlskogSectorAxisMinimalProducerReceipt :
    CKMJarlskogSectorAxisMinimalProducerReceipt where
  full_surface_to_sector_axis :=
    rationalStencilCarrierCoefficientSurface_to_sectorAxis
  canonical_sector_axis :=
    canonical_rationalStencilSectorAxisSourceEquations
  jarlskog_normal_form :=
    ckmJarlskogDepthSum_gridOfStencil_eq_twice_sectorAxisGap
  sector_axis_forces_386 :=
    rationalStencilSectorAxisSourceEquations_jarlskogDepthSum_eq_386
  carrier_gap := rationalSectorAxisCarrierGap_eq_193
  twice_carrier_gap := twice_rationalSectorAxisCarrierGap_eq_386

end StandardModelConstraint
end SaturationMonoid
