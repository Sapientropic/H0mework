import H0mework.Physics.MixingSources.P614

/-!
# Proposition 615: coefficient-surface no-choice theorem for Yukawa/CKM

P593 collects the carrier-sourced Yukawa stencil coefficients.  P614 shows
that the Jarlskog depth sum is twice one sector-axis coefficient gap.  This
file removes another possible escape hatch:

* any rational biquadratic stencil whose nine coefficients are the
  carrier-sourced coefficient vector is the canonical P584/P586 stencil;
* therefore its full `3 x 3` Yukawa depth grid is the selected grid;
* therefore its mass-order depth list and Jarlskog depth sum are forced.

Boundary: this is still a finite coefficient-surface theorem.  It does not
derive the carrier coefficient vector from continuous SU(7)-breaking dynamics.
It proves that once that vector is produced, there is no residual freedom to
alter the nine depths or the CKM/Jarlskog `386`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Coefficient vectors as rational stencils -/

/-- Read an integer coefficient vector as a rational biquadratic stencil. -/
def rationalStencilOfCoefficientVector
    (V : YukawaDepthStencilCoefficientVector) :
    RationalYukawaBiquadraticStencil where
  center := V.center
  generationSlope := V.generationSlope
  sectorSlope := V.sectorSlope
  generationCurvature := V.generationCurvature
  sectorCurvature := V.sectorCurvature
  mixedTwist := V.mixedTwist
  generationCurvatureSector := V.generationCurvatureSector
  generationSectorCurvature := V.generationSectorCurvature
  bicurvature := V.bicurvature

/-- THEOREM 1: the carrier-sourced coefficient vector is exactly the canonical
rational Yukawa stencil. -/
theorem rationalStencilOf_carrierSourcedCoefficients_eq_canonical :
    rationalStencilOfCoefficientVector
        carrierSourcedYukawaDepthStencilCoefficientVector =
      RationalYukawaBiquadraticStencil.canonical := by
  ext <;>
    simp [rationalStencilOfCoefficientVector,
      carrierSourcedYukawaDepthStencilCoefficientVector,
      RationalYukawaBiquadraticStencil.canonical,
      visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
      informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
      yukawaDepthStencilCenter, yukawaDepthStencilGenerationSlope,
      yukawaDepthStencilSectorSlope, yukawaDepthStencilGenerationCurvature,
      yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
      yukawaDepthStencilGenerationCurvatureSector,
      yukawaDepthStencilGenerationSectorCurvature,
      yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
      canonicalInformationMatterSupportCardZ, alphaEMIntegerDenominator,
      su7GaugeFreedomDimension, sevenFacetInformationStateCount]

/-- Fieldwise carrier coefficient surface for rational stencils.  This is the
coefficient-level producer surface, not a grid/table surface. -/
def RationalStencilCarrierCoefficientSurface
    (C : RationalYukawaBiquadraticStencil) : Prop :=
  C.center =
      (carrierSourcedYukawaDepthStencilCoefficientVector.center : ℚ) ∧
    C.generationSlope =
      (carrierSourcedYukawaDepthStencilCoefficientVector.generationSlope : ℚ) ∧
    C.sectorSlope =
      (carrierSourcedYukawaDepthStencilCoefficientVector.sectorSlope : ℚ) ∧
    C.generationCurvature =
      (carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvature : ℚ) ∧
    C.sectorCurvature =
      (carrierSourcedYukawaDepthStencilCoefficientVector.sectorCurvature : ℚ) ∧
    C.mixedTwist =
      (carrierSourcedYukawaDepthStencilCoefficientVector.mixedTwist : ℚ) ∧
    C.generationCurvatureSector =
      (carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvatureSector : ℚ) ∧
    C.generationSectorCurvature =
      (carrierSourcedYukawaDepthStencilCoefficientVector.generationSectorCurvature : ℚ) ∧
    C.bicurvature =
      (carrierSourcedYukawaDepthStencilCoefficientVector.bicurvature : ℚ)

/-- THEOREM 2: the canonical stencil lies on the carrier coefficient surface. -/
theorem canonical_rationalStencilCarrierCoefficientSurface :
    RationalStencilCarrierCoefficientSurface
      RationalYukawaBiquadraticStencil.canonical := by
  have h :=
    rationalStencilOf_carrierSourcedCoefficients_eq_canonical.symm
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.center h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.generationSlope h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.sectorSlope h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.generationCurvature h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.sectorCurvature h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.mixedTwist h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.generationCurvatureSector h
  constructor
  · exact congrArg RationalYukawaBiquadraticStencil.generationSectorCurvature h
  · exact congrArg RationalYukawaBiquadraticStencil.bicurvature h

/-- THEOREM 3: a rational stencil is on the carrier coefficient surface iff it
is the canonical stencil.  This is the no-choice point: once the coefficient
carrier is fixed, no second `3 x 3` Yukawa stencil remains. -/
theorem rationalStencilCarrierCoefficientSurface_iff_eq_canonical
    (C : RationalYukawaBiquadraticStencil) :
    RationalStencilCarrierCoefficientSurface C ↔
      C = RationalYukawaBiquadraticStencil.canonical := by
  constructor
  · intro hC
    rcases hC with
      ⟨hCenter, hGenerationSlope, hSectorSlope, hGenerationCurvature,
        hSectorCurvature, hMixedTwist, hGenerationCurvatureSector,
        hGenerationSectorCurvature, hBicurvature⟩
    have hvec :
        C =
          rationalStencilOfCoefficientVector
            carrierSourcedYukawaDepthStencilCoefficientVector := by
      ext <;>
        simp [rationalStencilOfCoefficientVector, hCenter,
          hGenerationSlope, hSectorSlope, hGenerationCurvature,
          hSectorCurvature, hMixedTwist, hGenerationCurvatureSector,
          hGenerationSectorCurvature, hBicurvature]
    rw [hvec, rationalStencilOf_carrierSourcedCoefficients_eq_canonical]
  · intro hC
    rw [hC]
    exact canonical_rationalStencilCarrierCoefficientSurface

/-! ## Forced grid, mass order, and Jarlskog sum -/

/-- The Yukawa depth grid generated directly from the carrier coefficient
vector. -/
def carrierCoefficientYukawaDepthGrid : RationalYukawaDepthGrid :=
  gridOfStencil
    (rationalStencilOfCoefficientVector
      carrierSourcedYukawaDepthStencilCoefficientVector)

/-- THEOREM 4: the carrier coefficient vector generates exactly the selected
Yukawa depth grid. -/
theorem carrierCoefficientYukawaDepthGrid_eq_selected :
    carrierCoefficientYukawaDepthGrid = selectedYukawaDepthGrid := by
  rw [carrierCoefficientYukawaDepthGrid,
    rationalStencilOf_carrierSourcedCoefficients_eq_canonical,
    ← selectedGrid_eq_gridOf_canonical]

/-- Read a named Yukawa parameter from a rational grid. -/
def rationalGridDepthOf
    (G : RationalYukawaDepthGrid) (y : YukawaParameter) : ℚ :=
  G (yukawaMatrixCoordinates y).1 (yukawaMatrixCoordinates y).2

/-- The rational-grid mass-order list, in the same order used by the integer
depth receipts. -/
def rationalGridMassOrder (G : RationalYukawaDepthGrid) : List ℚ :=
  [ rationalGridDepthOf G .top
  , rationalGridDepthOf G .bottom
  , rationalGridDepthOf G .tau
  , rationalGridDepthOf G .charm
  , rationalGridDepthOf G .muon
  , rationalGridDepthOf G .strange
  , rationalGridDepthOf G .down
  , rationalGridDepthOf G .up
  , rationalGridDepthOf G .electron
  ]

/-- THEOREM 5: the carrier coefficient vector forces the documented nine
Yukawa depths. -/
theorem carrierCoefficientYukawaDepthGrid_massOrder_eq :
    rationalGridMassOrder carrierCoefficientYukawaDepthGrid =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rw [carrierCoefficientYukawaDepthGrid_eq_selected]
  rfl

/-- Jarlskog four-product depth sum read from a rational grid. -/
def ckmJarlskogDepthSumFromRationalGrid
    (G : RationalYukawaDepthGrid) : ℚ :=
  (rationalGridDepthOf G .strange - rationalGridDepthOf G .up) +
    (rationalGridDepthOf G .bottom - rationalGridDepthOf G .charm) +
      (rationalGridDepthOf G .up - rationalGridDepthOf G .bottom) +
        (rationalGridDepthOf G .strange - rationalGridDepthOf G .charm)

/-- THEOREM 6: the carrier coefficient vector forces the CKM/Jarlskog depth
sum `386`. -/
theorem carrierCoefficientYukawaDepthGrid_jarlskogDepthSum_eq_386 :
    ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid =
      (386 : ℚ) := by
  rw [carrierCoefficientYukawaDepthGrid_eq_selected]
  norm_num [ckmJarlskogDepthSumFromRationalGrid, rationalGridDepthOf,
    selectedYukawaDepthGrid, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth, yukawaMatrixCoordinates,
    yukawaMatrixParameter]

/-- THEOREM 7: every rational stencil on the carrier coefficient surface has
the selected grid. -/
theorem rationalStencilCarrierCoefficientSurface_grid_eq_selected
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilCarrierCoefficientSurface C) :
    gridOfStencil C = selectedYukawaDepthGrid := by
  rw [(rationalStencilCarrierCoefficientSurface_iff_eq_canonical C).mp hC,
    ← selectedGrid_eq_gridOf_canonical]

/-- THEOREM 8: every rational stencil on the carrier coefficient surface has
the documented mass-order depth list. -/
theorem rationalStencilCarrierCoefficientSurface_massOrder_eq
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilCarrierCoefficientSurface C) :
    rationalGridMassOrder (gridOfStencil C) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rw [rationalStencilCarrierCoefficientSurface_grid_eq_selected C hC]
  rfl

/-- THEOREM 9: every rational stencil on the carrier coefficient surface has
the CKM/Jarlskog depth sum `386`. -/
theorem rationalStencilCarrierCoefficientSurface_jarlskogDepthSum_eq_386
    (C : RationalYukawaBiquadraticStencil)
    (hC : RationalStencilCarrierCoefficientSurface C) :
    ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
      (386 : ℚ) := by
  rw [rationalStencilCarrierCoefficientSurface_grid_eq_selected C hC]
  norm_num [ckmJarlskogDepthSumFromRationalGrid, rationalGridDepthOf,
    selectedYukawaDepthGrid, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth, yukawaMatrixCoordinates,
    yukawaMatrixParameter]

/-! ## Bundled receipt -/

/-- Compact receipt: the carrier-sourced coefficient vector is a no-choice
producer for the selected Yukawa grid and CKM/Jarlskog depth sum. -/
structure YukawaCarrierCoefficientNoChoiceReceipt where
  carrier_coefficients_eq_canonical :
    rationalStencilOfCoefficientVector
        carrierSourcedYukawaDepthStencilCoefficientVector =
      RationalYukawaBiquadraticStencil.canonical
  surface_iff_canonical :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ↔
        C = RationalYukawaBiquadraticStencil.canonical
  carrier_grid :
    carrierCoefficientYukawaDepthGrid = selectedYukawaDepthGrid
  carrier_mass_order :
    rationalGridMassOrder carrierCoefficientYukawaDepthGrid =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  carrier_jarlskog :
    ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid =
      (386 : ℚ)
  all_surface_grids :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ->
        gridOfStencil C = selectedYukawaDepthGrid
  all_surface_mass_order :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ->
        rationalGridMassOrder (gridOfStencil C) =
          [50, 346, 372, 489, 583, 682, 880, 908, 982]
  all_surface_jarlskog :
    ∀ C : RationalYukawaBiquadraticStencil,
      RationalStencilCarrierCoefficientSurface C ->
        ckmJarlskogDepthSumFromRationalGrid (gridOfStencil C) =
          (386 : ℚ)

/-- THEOREM 10: no-choice receipt for the carrier coefficient surface. -/
theorem yukawaCarrierCoefficientNoChoiceReceipt :
    YukawaCarrierCoefficientNoChoiceReceipt where
  carrier_coefficients_eq_canonical :=
    rationalStencilOf_carrierSourcedCoefficients_eq_canonical
  surface_iff_canonical :=
    rationalStencilCarrierCoefficientSurface_iff_eq_canonical
  carrier_grid := carrierCoefficientYukawaDepthGrid_eq_selected
  carrier_mass_order := carrierCoefficientYukawaDepthGrid_massOrder_eq
  carrier_jarlskog :=
    carrierCoefficientYukawaDepthGrid_jarlskogDepthSum_eq_386
  all_surface_grids :=
    rationalStencilCarrierCoefficientSurface_grid_eq_selected
  all_surface_mass_order :=
    rationalStencilCarrierCoefficientSurface_massOrder_eq
  all_surface_jarlskog :=
    rationalStencilCarrierCoefficientSurface_jarlskogDepthSum_eq_386

end StandardModelConstraint
end SaturationMonoid
