import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P586

/-!
# Proposition 587: finite-difference coordinates for the Yukawa depth grid

P586 proves uniqueness of the centered biquadratic stencil for the selected
`3 x 3` Yukawa depth grid.  This file makes the coordinate transform explicit:

* a depth grid is a function on `generation x interaction-sector`;
* its nine centered finite differences are exactly the nine biquadratic
  stencil coefficients;
* converting a stencil to its grid and back is identity;
* converting any grid to finite-difference stencil and back is identity.

Thus P584's coefficient vector is not another table.  It is the finite
difference coordinate system of the `3 x 3` Yukawa carrier.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open RationalYukawaBiquadraticStencil

/-- A rational-valued depth grid on the `3 x 3` Yukawa matrix carrier. -/
abbrev RationalYukawaDepthGrid :=
  StandardModelFermionGeneration -> YukawaInteractionSector -> ℚ

/-- The grid sampled from a rational biquadratic stencil. -/
def gridOfStencil (C : RationalYukawaBiquadraticStencil) :
    RationalYukawaDepthGrid :=
  fun g s => C.eval g s

/-- The selected nine-depth grid, in matrix coordinates. -/
def selectedYukawaDepthGrid : RationalYukawaDepthGrid :=
  fun g s => (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ)

/-- Finite-difference extraction of the centered biquadratic stencil
coordinates from an arbitrary `3 x 3` depth grid. -/
def stencilFromGrid (G : RationalYukawaDepthGrid) :
    RationalYukawaBiquadraticStencil where
  center :=
    G .second .downLike
  generationSlope :=
    (G .first .downLike - G .third .downLike) / 2
  sectorSlope :=
    (G .second .chargedLepton - G .second .upLike) / 2
  generationCurvature :=
    (G .first .downLike + G .third .downLike -
      2 * G .second .downLike) / 2
  sectorCurvature :=
    (G .second .chargedLepton + G .second .upLike -
      2 * G .second .downLike) / 2
  mixedTwist :=
    (G .first .chargedLepton - G .first .upLike -
      G .third .chargedLepton + G .third .upLike) / 4
  generationCurvatureSector :=
    (G .first .chargedLepton + G .third .chargedLepton -
      2 * G .second .chargedLepton -
      G .first .upLike - G .third .upLike +
      2 * G .second .upLike) / 4
  generationSectorCurvature :=
    (G .first .chargedLepton + G .first .upLike -
      2 * G .first .downLike -
      G .third .chargedLepton - G .third .upLike +
      2 * G .third .downLike) / 4
  bicurvature :=
    (G .first .chargedLepton + G .third .chargedLepton -
      2 * G .second .chargedLepton +
      G .first .upLike + G .third .upLike -
      2 * G .second .upLike -
      2 * G .first .downLike - 2 * G .third .downLike +
      4 * G .second .downLike) / 4

/-- THEOREM 1: finite differences recover the coefficients of any stencil. -/
theorem stencilFromGrid_gridOfStencil
    (C : RationalYukawaBiquadraticStencil) :
    stencilFromGrid (gridOfStencil C) = C := by
  rcases C with
    ⟨center, generationSlope, sectorSlope, generationCurvature,
      sectorCurvature, mixedTwist, generationCurvatureSector,
      generationSectorCurvature, bicurvature⟩
  ext <;>
    norm_num [stencilFromGrid, gridOfStencil, eval,
      yukawaGenerationDepthCoordinate, yukawaSectorDepthCoordinate] <;>
    ring

/-- THEOREM 2: every `3 x 3` grid is exactly reconstructed by its
finite-difference biquadratic stencil. -/
theorem gridOfStencil_stencilFromGrid
    (G : RationalYukawaDepthGrid) :
    gridOfStencil (stencilFromGrid G) = G := by
  funext g s
  cases g <;> cases s <;>
    norm_num [gridOfStencil, stencilFromGrid, eval,
      yukawaGenerationDepthCoordinate, yukawaSectorDepthCoordinate] <;>
    ring

/-- THEOREM 3: the selected grid's finite-difference stencil is P586's
canonical stencil. -/
theorem stencilFromGrid_selected_eq_canonical :
    stencilFromGrid selectedYukawaDepthGrid =
      RationalYukawaBiquadraticStencil.canonical := by
  have hgrid :
      selectedYukawaDepthGrid =
        gridOfStencil RationalYukawaBiquadraticStencil.canonical := by
    funext g s
    exact (RationalYukawaBiquadraticStencil.canonical_eval_eq_selectedDepth
      g s).symm
  rw [hgrid]
  exact stencilFromGrid_gridOfStencil
    RationalYukawaBiquadraticStencil.canonical

/-- THEOREM 4: the selected grid is the grid of the canonical stencil. -/
theorem selectedGrid_eq_gridOf_canonical :
    selectedYukawaDepthGrid =
      gridOfStencil RationalYukawaBiquadraticStencil.canonical := by
  funext g s
  exact (RationalYukawaBiquadraticStencil.canonical_eval_eq_selectedDepth
    g s).symm

/-- THEOREM 5: the selected finite-difference coordinates evaluate to the P584
integer carrier-card coefficient tuple. -/
theorem selectedGrid_finiteDifferenceCoordinates_eq :
    (stencilFromGrid selectedYukawaDepthGrid).center = 682 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSlope = 267 ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorSlope = 47 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvature = -69 ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature = -146 ∧
      (stencilFromGrid selectedYukawaDepthGrid).mixedTwist = -62 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvatureSector = 52 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSectorCurvature = 100 ∧
      (stencilFromGrid selectedYukawaDepthGrid).bicurvature = 111 := by
  rw [stencilFromGrid_selected_eq_canonical]
  exact RationalYukawaBiquadraticStencil.canonical_coefficients_eq

/-- Compact receipt: the selected `3 x 3` Yukawa depth object is equivalently a
grid or its centered finite-difference stencil. -/
structure YukawaDepthFiniteDifferenceReceipt where
  stencil_to_grid_to_stencil :
    ∀ C : RationalYukawaBiquadraticStencil,
      stencilFromGrid (gridOfStencil C) = C
  grid_to_stencil_to_grid :
    ∀ G : RationalYukawaDepthGrid,
      gridOfStencil (stencilFromGrid G) = G
  selected_stencil :
    stencilFromGrid selectedYukawaDepthGrid =
      RationalYukawaBiquadraticStencil.canonical
  selected_grid :
    selectedYukawaDepthGrid =
      gridOfStencil RationalYukawaBiquadraticStencil.canonical
  selected_coordinates :
    (stencilFromGrid selectedYukawaDepthGrid).center = 682 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSlope = 267 ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorSlope = 47 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvature = -69 ∧
      (stencilFromGrid selectedYukawaDepthGrid).sectorCurvature = -146 ∧
      (stencilFromGrid selectedYukawaDepthGrid).mixedTwist = -62 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationCurvatureSector = 52 ∧
      (stencilFromGrid selectedYukawaDepthGrid).generationSectorCurvature = 100 ∧
      (stencilFromGrid selectedYukawaDepthGrid).bicurvature = 111

/-- THEOREM 6: finite-difference receipt for the selected Yukawa depth grid. -/
theorem yukawaDepthFiniteDifferenceReceipt :
    YukawaDepthFiniteDifferenceReceipt where
  stencil_to_grid_to_stencil := stencilFromGrid_gridOfStencil
  grid_to_stencil_to_grid := gridOfStencil_stencilFromGrid
  selected_stencil := stencilFromGrid_selected_eq_canonical
  selected_grid := selectedGrid_eq_gridOf_canonical
  selected_coordinates := selectedGrid_finiteDifferenceCoordinates_eq

end StandardModelConstraint
end SaturationMonoid
