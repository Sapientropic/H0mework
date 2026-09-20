import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P588

/-!
# Proposition 589: Poincare/sector coordinates for the Yukawa depth stencil

P587 made the selected Yukawa table equivalent to its centered finite
differences.  P588 routed the coefficient cards to existing finite carrier
producers.  This file routes the two stencil axes themselves:

* the generation coordinate is the reversed coordinate of the 4D Poincare
  orbit index `scalar/volume -> connection/current -> curvature`;
* the interaction-sector coordinate is the centered coordinate of the
  `up-like -> down-like -> charged-lepton` sector index.

Thus the same nine-depth table is now read from

`Poincare orbit coordinate x interaction-sector coordinate`

with the P588 carrier-source coefficients.  This still does not prove the
physical SU(7) dynamics that selects the coordinate polynomial; it removes the
remaining hand-written coordinate-axis debt from the finite producer layer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Poincare-sourced generation coordinate -/

/-- The ordered finite orbit index of the 4D Poincare generation slots. -/
def poincareSlotOrbitIndexZ :
    FourDimensionalPoincareSlot -> Int
  | .scalarVolume => 0
  | .connectionCurrent => 1
  | .curvature => 2

/-- The centered depth coordinate induced by the Poincare orbit index.

The coordinate is reversed because the selected depth hierarchy places the
curvature/third-generation slot at the low-depth end and the scalar/first slot
at the high-depth end. -/
def poincareSlotDepthCoordinateZ
    (s : FourDimensionalPoincareSlot) : Int :=
  1 - poincareSlotOrbitIndexZ s

/-- THEOREM 1: Poincare slot coordinates are `1, 0, -1`. -/
theorem poincareSlotDepthCoordinateZ_values :
    poincareSlotDepthCoordinateZ .scalarVolume = 1 ∧
      poincareSlotDepthCoordinateZ .connectionCurrent = 0 ∧
      poincareSlotDepthCoordinateZ .curvature = -1 := by
  norm_num [poincareSlotDepthCoordinateZ, poincareSlotOrbitIndexZ]

/-- THEOREM 2: P584's generation coordinate is exactly the Poincare orbit
coordinate of the Standard-Model generation slot. -/
theorem yukawaGenerationDepthCoordinate_eq_poincareSlotCoordinate
    (g : StandardModelFermionGeneration) :
    yukawaGenerationDepthCoordinate g =
      poincareSlotDepthCoordinateZ
        (standardModelGenerationPoincareSlot g) := by
  cases g <;>
    norm_num [yukawaGenerationDepthCoordinate,
      poincareSlotDepthCoordinateZ, poincareSlotOrbitIndexZ,
      standardModelGenerationPoincareSlot]

/-! ## Sector-sourced interaction coordinate -/

/-- The ordered finite index of the three Yukawa interaction sectors. -/
def yukawaInteractionSectorIndexZ :
    YukawaInteractionSector -> Int
  | .upLike => 0
  | .downLike => 1
  | .chargedLepton => 2

/-- The centered interaction-sector coordinate. -/
def yukawaInteractionSectorCoordinateZ
    (s : YukawaInteractionSector) : Int :=
  yukawaInteractionSectorIndexZ s - 1

/-- THEOREM 3: interaction-sector coordinates are `-1, 0, 1`. -/
theorem yukawaInteractionSectorCoordinateZ_values :
    yukawaInteractionSectorCoordinateZ .upLike = -1 ∧
      yukawaInteractionSectorCoordinateZ .downLike = 0 ∧
      yukawaInteractionSectorCoordinateZ .chargedLepton = 1 := by
  norm_num [yukawaInteractionSectorCoordinateZ,
    yukawaInteractionSectorIndexZ]

/-- THEOREM 4: P584's sector coordinate is exactly the centered sector-index
coordinate. -/
theorem yukawaSectorDepthCoordinate_eq_interactionSectorCoordinate
    (s : YukawaInteractionSector) :
    yukawaSectorDepthCoordinate s =
      yukawaInteractionSectorCoordinateZ s := by
  cases s <;>
    norm_num [yukawaSectorDepthCoordinate,
      yukawaInteractionSectorCoordinateZ, yukawaInteractionSectorIndexZ]

/-! ## Carrier-source stencil using Poincare/sector coordinates -/

/-- The Poincare/sector sourced Yukawa depth stencil with P588's carrier-source
coefficient cards. -/
def poincareSectorSourcedYukawaDepthStencilAt
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) : Int :=
  let x :=
    poincareSlotDepthCoordinateZ
      (standardModelGenerationPoincareSlot g)
  let y := yukawaInteractionSectorCoordinateZ s
  (5 * alphaEMIntegerDenominator ℤ - 3) +
    (2 * alphaEMIntegerDenominator ℤ - 7) * x +
    (su7GaugeFreedomDimension ℤ - 1) * y +
    (-((alphaEMIntegerDenominator ℤ + 1) / 2)) * (x ^ (2 : Nat)) +
    (-(alphaEMIntegerDenominator ℤ +
      visibleGaugeCarrierCardFromLowEnergyZ)) * (y ^ (2 : Nat)) +
    (-(su7GaugeFreedomDimension ℤ + 2 * (7 : Int))) * x * y +
    (su7GaugeFreedomDimension ℤ + 4) * (x ^ (2 : Nat)) * y +
    ((visibleGaugeCarrierCardFromLowEnergyZ + 1) ^ (2 : Nat)) *
      x * (y ^ (2 : Nat)) +
    (sevenFacetInformationStateCount ℤ -
      informationMatterSupportCardFromComponentCarrierZ) *
      (x ^ (2 : Nat)) * (y ^ (2 : Nat))

/-- The same sourced stencil read on a named Yukawa row. -/
def poincareSectorSourcedYukawaDepthStencilOf
    (y : YukawaParameter) : Int :=
  poincareSectorSourcedYukawaDepthStencilAt
    (yukawaMatrixCoordinates y).1 (yukawaMatrixCoordinates y).2

/-- THEOREM 5: the Poincare/sector sourced stencil is definitionally the same
finite matrix as P584's carrier-card stencil. -/
theorem poincareSectorSourcedYukawaDepthStencilAt_eq_stencil
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) :
    poincareSectorSourcedYukawaDepthStencilAt g s =
      yukawaDepthStencilAt g s := by
  cases g <;> cases s <;>
    norm_num [poincareSectorSourcedYukawaDepthStencilAt,
      yukawaDepthStencilAt, poincareSlotDepthCoordinateZ,
      poincareSlotOrbitIndexZ, standardModelGenerationPoincareSlot,
      yukawaInteractionSectorCoordinateZ, yukawaInteractionSectorIndexZ,
      yukawaGenerationDepthCoordinate, yukawaSectorDepthCoordinate,
      yukawaDepthStencilCenter, yukawaDepthStencilGenerationSlope,
      yukawaDepthStencilSectorSlope, yukawaDepthStencilGenerationCurvature,
      yukawaDepthStencilSectorCurvature, yukawaDepthStencilMixedTwist,
      yukawaDepthStencilGenerationCurvatureSector,
      yukawaDepthStencilGenerationSectorCurvature,
      yukawaDepthStencilBicurvature,
      visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
      informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
      visibleGaugeCarrierCardZ, canonicalInformationMatterSupportCardZ,
      alphaEMIntegerDenominator, sevenFacetInformationStateCount,
      su7GaugeFreedomDimension]

/-- THEOREM 6: the Poincare/sector sourced stencil reproduces the selected
Yukawa depth table. -/
theorem poincareSectorSourcedYukawaDepthStencilOf_eq_selectedDepthZ
    (y : YukawaParameter) :
    poincareSectorSourcedYukawaDepthStencilOf y =
      selectedYukawaIntegerDepthZ y := by
  unfold poincareSectorSourcedYukawaDepthStencilOf
  rw [poincareSectorSourcedYukawaDepthStencilAt_eq_stencil]
  simpa [yukawaDepthStencilOf] using
    yukawaDepthStencilOf_eq_selectedDepthZ y

/-- THEOREM 7: after converting to natural depth, the selected SU(7) seed's
Yukawa depth field is the Poincare/sector sourced stencil. -/
theorem selectedSU7_yukawaDepth_eq_poincareSectorSourcedStencil
    (y : YukawaParameter) :
    selectedDiscreteStandardModelSeed.su7.yukawaDepth y =
      (poincareSectorSourcedYukawaDepthStencilOf y).toNat := by
  rw [poincareSectorSourcedYukawaDepthStencilOf_eq_selectedDepthZ]
  cases y <;> rfl

/-- THEOREM 8: the CKM/Jarlskog depth sum is read from the same
Poincare/sector sourced stencil. -/
theorem ckmDepthSum_fromPoincareSectorSourcedStencil_eq_386 :
    (poincareSectorSourcedYukawaDepthStencilOf .strange -
        poincareSectorSourcedYukawaDepthStencilOf .up) +
      (poincareSectorSourcedYukawaDepthStencilOf .bottom -
        poincareSectorSourcedYukawaDepthStencilOf .charm) +
      (poincareSectorSourcedYukawaDepthStencilOf .up -
        poincareSectorSourcedYukawaDepthStencilOf .bottom) +
      (poincareSectorSourcedYukawaDepthStencilOf .strange -
        poincareSectorSourcedYukawaDepthStencilOf .charm) =
        (ckmCPDepthSum : Int) := by
  repeat rw [poincareSectorSourcedYukawaDepthStencilOf_eq_selectedDepthZ]
  simpa [ckmDepthSum_fromYukawaDepths,
    ckmDepthDelta_us_fromYukawaDepths,
    ckmDepthDelta_cb_fromYukawaDepths,
    ckmDepthDelta_ub_conj_fromYukawaDepths,
    ckmDepthDelta_cs_conj_fromYukawaDepths] using
    ckmDepthSum_fromYukawaDepths_eq_386

/-! ## Bundled receipt -/

/-- Compact receipt: the selected Yukawa depth table is produced by the
Poincare-orbit coordinate crossed with the Yukawa interaction-sector
coordinate, using the P588 carrier-source coefficient cards. -/
structure PoincareSectorSourcedYukawaDepthReceipt where
  poincare_coordinate_values :
    poincareSlotDepthCoordinateZ .scalarVolume = 1 ∧
      poincareSlotDepthCoordinateZ .connectionCurrent = 0 ∧
      poincareSlotDepthCoordinateZ .curvature = -1
  generation_coordinate_source :
    ∀ g : StandardModelFermionGeneration,
      yukawaGenerationDepthCoordinate g =
        poincareSlotDepthCoordinateZ
          (standardModelGenerationPoincareSlot g)
  sector_coordinate_values :
    yukawaInteractionSectorCoordinateZ .upLike = -1 ∧
      yukawaInteractionSectorCoordinateZ .downLike = 0 ∧
      yukawaInteractionSectorCoordinateZ .chargedLepton = 1
  sector_coordinate_source :
    ∀ s : YukawaInteractionSector,
      yukawaSectorDepthCoordinate s =
        yukawaInteractionSectorCoordinateZ s
  sourced_stencil_eq :
    ∀ g s,
      poincareSectorSourcedYukawaDepthStencilAt g s =
        yukawaDepthStencilAt g s
  reproduces_depths :
    ∀ y : YukawaParameter,
      selectedDiscreteStandardModelSeed.su7.yukawaDepth y =
        (poincareSectorSourcedYukawaDepthStencilOf y).toNat
  ckm_depth_sum :
    (poincareSectorSourcedYukawaDepthStencilOf .strange -
        poincareSectorSourcedYukawaDepthStencilOf .up) +
      (poincareSectorSourcedYukawaDepthStencilOf .bottom -
        poincareSectorSourcedYukawaDepthStencilOf .charm) +
      (poincareSectorSourcedYukawaDepthStencilOf .up -
        poincareSectorSourcedYukawaDepthStencilOf .bottom) +
      (poincareSectorSourcedYukawaDepthStencilOf .strange -
        poincareSectorSourcedYukawaDepthStencilOf .charm) =
        (ckmCPDepthSum : Int)

/-- THEOREM 9: Poincare/sector sourced depth receipt. -/
theorem poincareSectorSourcedYukawaDepthReceipt :
    PoincareSectorSourcedYukawaDepthReceipt where
  poincare_coordinate_values :=
    poincareSlotDepthCoordinateZ_values
  generation_coordinate_source :=
    yukawaGenerationDepthCoordinate_eq_poincareSlotCoordinate
  sector_coordinate_values :=
    yukawaInteractionSectorCoordinateZ_values
  sector_coordinate_source :=
    yukawaSectorDepthCoordinate_eq_interactionSectorCoordinate
  sourced_stencil_eq :=
    poincareSectorSourcedYukawaDepthStencilAt_eq_stencil
  reproduces_depths :=
    selectedSU7_yukawaDepth_eq_poincareSectorSourcedStencil
  ckm_depth_sum :=
    ckmDepthSum_fromPoincareSectorSourcedStencil_eq_386

end StandardModelConstraint
end SaturationMonoid
