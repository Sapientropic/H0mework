import Mathlib.Tactic
import H0mework.Physics.JointSources.P585

/-!
# Proposition 586: uniqueness of the 3x3 Yukawa depth stencil

P584 gives one centered biquadratic stencil whose values on the
`generation x interaction-sector` carrier are the selected nine Yukawa depths.
This file proves the finite interpolation fact behind that move:

* on the three-by-three grid with coordinates `{-1,0,1} x {-1,0,1}`,
  the nine biquadratic coefficients are uniquely determined by the nine grid
  values;
* the P584 stencil is exactly that unique coefficient vector for the selected
  Yukawa depth grid.

Boundary: this still uses the selected depth grid as input.  It proves
canonicality of the stencil coordinate system, not the deeper SU(7) dynamics
that must ultimately produce the grid itself.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- Rational coefficient vector for a centered biquadratic stencil on the
`3 x 3` Yukawa matrix carrier.  Over `ℚ`, the interpolation map is cleanly
invertible; P584 separately proves the selected coefficients are in fact
integers. -/
@[ext]
structure RationalYukawaBiquadraticStencil where
  center : ℚ
  generationSlope : ℚ
  sectorSlope : ℚ
  generationCurvature : ℚ
  sectorCurvature : ℚ
  mixedTwist : ℚ
  generationCurvatureSector : ℚ
  generationSectorCurvature : ℚ
  bicurvature : ℚ

namespace RationalYukawaBiquadraticStencil

/-- Evaluate a rational biquadratic stencil at a generation/sector cell. -/
def eval (C : RationalYukawaBiquadraticStencil)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) : ℚ :=
  let x : ℚ := yukawaGenerationDepthCoordinate g
  let y : ℚ := yukawaSectorDepthCoordinate s
  C.center +
    C.generationSlope * x +
    C.sectorSlope * y +
    C.generationCurvature * (x ^ (2 : Nat)) +
    C.sectorCurvature * (y ^ (2 : Nat)) +
    C.mixedTwist * x * y +
    C.generationCurvatureSector * (x ^ (2 : Nat)) * y +
    C.generationSectorCurvature * x * (y ^ (2 : Nat)) +
    C.bicurvature * (x ^ (2 : Nat)) * (y ^ (2 : Nat))

/-- The P584 finite carrier-card stencil, viewed over `ℚ`. -/
def canonical : RationalYukawaBiquadraticStencil where
  center := yukawaDepthStencilCenter
  generationSlope := yukawaDepthStencilGenerationSlope
  sectorSlope := yukawaDepthStencilSectorSlope
  generationCurvature := yukawaDepthStencilGenerationCurvature
  sectorCurvature := yukawaDepthStencilSectorCurvature
  mixedTwist := yukawaDepthStencilMixedTwist
  generationCurvatureSector := yukawaDepthStencilGenerationCurvatureSector
  generationSectorCurvature := yukawaDepthStencilGenerationSectorCurvature
  bicurvature := yukawaDepthStencilBicurvature

/-- THEOREM 1: the canonical rational stencil has the concrete coefficient
tuple from P584. -/
theorem canonical_coefficients_eq :
    canonical.center = 682 ∧
      canonical.generationSlope = 267 ∧
      canonical.sectorSlope = 47 ∧
      canonical.generationCurvature = -69 ∧
      canonical.sectorCurvature = -146 ∧
      canonical.mixedTwist = -62 ∧
      canonical.generationCurvatureSector = 52 ∧
      canonical.generationSectorCurvature = 100 ∧
      canonical.bicurvature = 111 := by
  norm_num [canonical, yukawaDepthStencilCenter,
    yukawaDepthStencilGenerationSlope, yukawaDepthStencilSectorSlope,
    yukawaDepthStencilGenerationCurvature,
    yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
    yukawaDepthStencilGenerationCurvatureSector,
    yukawaDepthStencilGenerationSectorCurvature,
    yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
    alphaEMIntegerDenominator, sevenFacetInformationStateCount,
    su7GaugeFreedomDimension, canonicalInformationMatterSupportCardZ]

/-- THEOREM 2: the canonical rational stencil reproduces the selected Yukawa
depth grid. -/
theorem canonical_eval_eq_selectedDepth
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    canonical.eval g s =
      (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ) := by
  cases g <;> cases s <;>
    norm_num [eval, canonical, yukawaMatrixParameter,
      yukawaGenerationDepthCoordinate, yukawaSectorDepthCoordinate,
      yukawaDepthStencilCenter, yukawaDepthStencilGenerationSlope,
      yukawaDepthStencilSectorSlope, yukawaDepthStencilGenerationCurvature,
      yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
      yukawaDepthStencilGenerationCurvatureSector,
      yukawaDepthStencilGenerationSectorCurvature,
      yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
      alphaEMIntegerDenominator, sevenFacetInformationStateCount,
      su7GaugeFreedomDimension, canonicalInformationMatterSupportCardZ,
      selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth]

/-- THEOREM 3: a rational biquadratic stencil on this centered `3 x 3` carrier
is uniquely determined by its nine selected Yukawa depth values. -/
theorem eq_canonical_of_eval_eq_selectedDepth
    (C : RationalYukawaBiquadraticStencil)
    (h : ∀ g s,
      C.eval g s =
        (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ)) :
    C = canonical := by
  rcases C with
    ⟨center, generationSlope, sectorSlope, generationCurvature,
      sectorCurvature, mixedTwist, generationCurvatureSector,
      generationSectorCurvature, bicurvature⟩
  have h00 := h .second .downLike
  have hm0 := h .third .downLike
  have hp0 := h .first .downLike
  have h0m := h .second .upLike
  have h0p := h .second .chargedLepton
  have hmm := h .third .upLike
  have hmp := h .third .chargedLepton
  have hpm := h .first .upLike
  have hpp := h .first .chargedLepton
  norm_num [eval, yukawaMatrixParameter, yukawaGenerationDepthCoordinate,
    yukawaSectorDepthCoordinate, selectedYukawaIntegerDepthZ,
    selectedYukawaIntegerDepth] at h00 hm0 hp0 h0m h0p hmm hmp hpm hpp
  ext <;>
    norm_num [canonical, yukawaDepthStencilCenter,
      yukawaDepthStencilGenerationSlope, yukawaDepthStencilSectorSlope,
      yukawaDepthStencilGenerationCurvature,
      yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
      yukawaDepthStencilGenerationCurvatureSector,
      yukawaDepthStencilGenerationSectorCurvature,
      yukawaDepthStencilBicurvature, visibleGaugeCarrierCardZ,
      alphaEMIntegerDenominator, sevenFacetInformationStateCount,
      su7GaugeFreedomDimension, canonicalInformationMatterSupportCardZ] <;>
    linarith

/-- THEOREM 4: the P584 integer stencil is the unique rational biquadratic
stencil for the selected `3 x 3` Yukawa depth grid. -/
theorem canonical_unique_for_selectedDepth :
    ∃! C : RationalYukawaBiquadraticStencil,
      ∀ g s,
        C.eval g s =
          (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ) := by
  refine ⟨canonical, canonical_eval_eq_selectedDepth, ?_⟩
  intro C hC
  exact eq_canonical_of_eval_eq_selectedDepth C hC

end RationalYukawaBiquadraticStencil

/-- A compact receipt for the canonical interpolation layer under P584. -/
structure YukawaDepthStencilUniquenessReceipt where
  canonical_coefficients :
    RationalYukawaBiquadraticStencil.canonical.center = 682 ∧
      RationalYukawaBiquadraticStencil.canonical.generationSlope = 267 ∧
      RationalYukawaBiquadraticStencil.canonical.sectorSlope = 47 ∧
      RationalYukawaBiquadraticStencil.canonical.generationCurvature = -69 ∧
      RationalYukawaBiquadraticStencil.canonical.sectorCurvature = -146 ∧
      RationalYukawaBiquadraticStencil.canonical.mixedTwist = -62 ∧
      RationalYukawaBiquadraticStencil.canonical.generationCurvatureSector = 52 ∧
      RationalYukawaBiquadraticStencil.canonical.generationSectorCurvature = 100 ∧
      RationalYukawaBiquadraticStencil.canonical.bicurvature = 111
  reproduces_grid :
    ∀ g s,
      RationalYukawaBiquadraticStencil.canonical.eval g s =
        (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ)
  unique :
    ∃! C : RationalYukawaBiquadraticStencil,
      ∀ g s,
        C.eval g s =
          (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ)

/-- THEOREM 5: uniqueness receipt for the selected Yukawa depth stencil. -/
theorem yukawaDepthStencilUniquenessReceipt :
    YukawaDepthStencilUniquenessReceipt where
  canonical_coefficients :=
    RationalYukawaBiquadraticStencil.canonical_coefficients_eq
  reproduces_grid :=
    RationalYukawaBiquadraticStencil.canonical_eval_eq_selectedDepth
  unique :=
    RationalYukawaBiquadraticStencil.canonical_unique_for_selectedDepth

end StandardModelConstraint
end SaturationMonoid
