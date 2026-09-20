import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P591

/-!
# Proposition 592: endpoint-preserving schedules leave the depth stencil fixed

P591 proved that an endpoint-signature preserving sector-to-incidence schedule
has no residual orientation freedom.  This file pushes that uniqueness through
the actual P589/P584 Yukawa depth stencil:

* replace the stencil's hand-read sector coordinate by the total SU(7)
  incidence coordinate read along an arbitrary endpoint-preserving schedule;
* prove that every such schedule gives the same nine Yukawa depths;
* prove that the CKM/Jarlskog depth sum remains `386`.

Boundary: this closes the finite endpoint-orientation producer layer.  It is
not yet a dynamical derivation of the stencil coefficients; it says that once
the P588 coefficients and the endpoint-signature convention are fixed, the
sector scheduling cannot tune the depth table or CKM phase sum.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection
open RunningSigmaBeta
open InformationMatterProjection

/-! ## Endpoint-parametrized sourced stencil -/

/-- The P588/P589 carrier-source depth stencil, but with its sector coordinate
read from a parameterized SU(7) incidence schedule. -/
def endpointScheduleSourcedYukawaDepthStencilAt
    (f : YukawaInteractionSector -> InformationSlot)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) : Int :=
  let x :=
    poincareSlotDepthCoordinateZ
      (standardModelGenerationPoincareSlot g)
  let y := yukawaSectorInformationIncidenceTotalCoordinateZ (f s)
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

/-- The endpoint-schedule sourced stencil read on a named Yukawa row. -/
def endpointScheduleSourcedYukawaDepthStencilOf
    (f : YukawaInteractionSector -> InformationSlot)
    (y : YukawaParameter) : Int :=
  endpointScheduleSourcedYukawaDepthStencilAt f
    (yukawaMatrixCoordinates y).1 (yukawaMatrixCoordinates y).2

/-! ## Endpoint-preserving schedules cannot change the depth table -/

/-- THEOREM 1: any endpoint-signature preserving schedule gives exactly the
P589 Poincare/sector sourced stencil. -/
theorem endpointScheduleSourcedYukawaDepthStencilAt_eq_poincareSector
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) :
    endpointScheduleSourcedYukawaDepthStencilAt f g s =
      poincareSectorSourcedYukawaDepthStencilAt g s := by
  rw [yukawaSectorEndpointSignaturePreservingSchedule_unique f hf]
  cases g <;> cases s <;>
    norm_num [endpointScheduleSourcedYukawaDepthStencilAt,
      poincareSectorSourcedYukawaDepthStencilAt,
      poincareSlotDepthCoordinateZ, poincareSlotOrbitIndexZ,
      standardModelGenerationPoincareSlot,
      yukawaSectorInformationIncidence,
      yukawaSectorInformationIncidenceTotalCoordinateZ,
      yukawaInteractionSectorCoordinateZ, yukawaInteractionSectorIndexZ]

/-- THEOREM 2: any endpoint-signature preserving schedule gives P584's
carrier-card depth stencil. -/
theorem endpointScheduleSourcedYukawaDepthStencilAt_eq_stencil
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) :
    endpointScheduleSourcedYukawaDepthStencilAt f g s =
      yukawaDepthStencilAt g s := by
  rw [endpointScheduleSourcedYukawaDepthStencilAt_eq_poincareSector f hf,
    poincareSectorSourcedYukawaDepthStencilAt_eq_stencil]

/-- THEOREM 3: any endpoint-signature preserving schedule reproduces the
selected integer Yukawa depth for each named row. -/
theorem endpointScheduleSourcedYukawaDepthStencilOf_eq_selectedDepthZ
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (y : YukawaParameter) :
    endpointScheduleSourcedYukawaDepthStencilOf f y =
      selectedYukawaIntegerDepthZ y := by
  unfold endpointScheduleSourcedYukawaDepthStencilOf
  rw [endpointScheduleSourcedYukawaDepthStencilAt_eq_poincareSector f hf]
  simpa [poincareSectorSourcedYukawaDepthStencilOf] using
    poincareSectorSourcedYukawaDepthStencilOf_eq_selectedDepthZ y

/-- THEOREM 4: after converting to natural depth, any endpoint-signature
preserving schedule gives the selected SU(7) seed's depth field. -/
theorem selectedSU7_yukawaDepth_eq_endpointScheduleSourcedStencil
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (y : YukawaParameter) :
    selectedDiscreteStandardModelSeed.su7.yukawaDepth y =
      (endpointScheduleSourcedYukawaDepthStencilOf f y).toNat := by
  rw [endpointScheduleSourcedYukawaDepthStencilOf_eq_selectedDepthZ f hf]
  cases y <;> rfl

/-- THEOREM 5: the mass-order depth list is invariant under every
endpoint-signature preserving sector schedule. -/
theorem endpointScheduleSourcedYukawaDepthStencil_massOrder_eq
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    [ (endpointScheduleSourcedYukawaDepthStencilOf f .top).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .bottom).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .tau).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .charm).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .muon).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .strange).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .down).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .up).toNat
    , (endpointScheduleSourcedYukawaDepthStencilOf f .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  repeat rw [endpointScheduleSourcedYukawaDepthStencilOf_eq_selectedDepthZ f hf]
  rfl

/-- THEOREM 6: the CKM/Jarlskog depth sum `386` is invariant under every
endpoint-signature preserving sector schedule. -/
theorem ckmDepthSum_fromEndpointScheduleSourcedStencil_eq_386
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    (endpointScheduleSourcedYukawaDepthStencilOf f .strange -
        endpointScheduleSourcedYukawaDepthStencilOf f .up) +
      (endpointScheduleSourcedYukawaDepthStencilOf f .bottom -
        endpointScheduleSourcedYukawaDepthStencilOf f .charm) +
      (endpointScheduleSourcedYukawaDepthStencilOf f .up -
        endpointScheduleSourcedYukawaDepthStencilOf f .bottom) +
      (endpointScheduleSourcedYukawaDepthStencilOf f .strange -
        endpointScheduleSourcedYukawaDepthStencilOf f .charm) =
        (ckmCPDepthSum : Int) := by
  repeat rw [endpointScheduleSourcedYukawaDepthStencilOf_eq_selectedDepthZ f hf]
  simpa [ckmDepthSum_fromYukawaDepths,
    ckmDepthDelta_us_fromYukawaDepths,
    ckmDepthDelta_cb_fromYukawaDepths,
    ckmDepthDelta_ub_conj_fromYukawaDepths,
    ckmDepthDelta_cs_conj_fromYukawaDepths] using
    ckmDepthSum_fromYukawaDepths_eq_386

/-! ## Bundled receipt -/

/-- Compact receipt: endpoint-signature preservation is strong enough to fix
the sourced Yukawa depth table and the CKM/Jarlskog depth sum. -/
structure EndpointScheduleSourcedYukawaDepthReceipt where
  schedule_collapses_to_poincare_sector :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      YukawaSectorEndpointSignaturePreservingSchedule f ->
        ∀ g s,
          endpointScheduleSourcedYukawaDepthStencilAt f g s =
            poincareSectorSourcedYukawaDepthStencilAt g s
  schedule_collapses_to_stencil :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      YukawaSectorEndpointSignaturePreservingSchedule f ->
        ∀ g s,
          endpointScheduleSourcedYukawaDepthStencilAt f g s =
            yukawaDepthStencilAt g s
  reproduces_depths :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        ∀ y : YukawaParameter,
          selectedDiscreteStandardModelSeed.su7.yukawaDepth y =
            (endpointScheduleSourcedYukawaDepthStencilOf f y).toNat
  mass_order :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        [ (endpointScheduleSourcedYukawaDepthStencilOf f .top).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .bottom).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .tau).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .charm).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .muon).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .strange).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .down).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .up).toNat
        , (endpointScheduleSourcedYukawaDepthStencilOf f .electron).toNat
        ] =
          [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ∀ f : YukawaInteractionSector -> InformationSlot,
      ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
        (endpointScheduleSourcedYukawaDepthStencilOf f .strange -
            endpointScheduleSourcedYukawaDepthStencilOf f .up) +
          (endpointScheduleSourcedYukawaDepthStencilOf f .bottom -
            endpointScheduleSourcedYukawaDepthStencilOf f .charm) +
          (endpointScheduleSourcedYukawaDepthStencilOf f .up -
            endpointScheduleSourcedYukawaDepthStencilOf f .bottom) +
          (endpointScheduleSourcedYukawaDepthStencilOf f .strange -
            endpointScheduleSourcedYukawaDepthStencilOf f .charm) =
            (ckmCPDepthSum : Int)

/-- THEOREM 7: endpoint-schedule sourced Yukawa depth receipt. -/
theorem endpointScheduleSourcedYukawaDepthReceipt :
    EndpointScheduleSourcedYukawaDepthReceipt where
  schedule_collapses_to_poincare_sector :=
    endpointScheduleSourcedYukawaDepthStencilAt_eq_poincareSector
  schedule_collapses_to_stencil :=
    endpointScheduleSourcedYukawaDepthStencilAt_eq_stencil
  reproduces_depths :=
    selectedSU7_yukawaDepth_eq_endpointScheduleSourcedStencil
  mass_order :=
    endpointScheduleSourcedYukawaDepthStencil_massOrder_eq
  ckm_depth_sum :=
    ckmDepthSum_fromEndpointScheduleSourcedStencil_eq_386

end StandardModelConstraint
end SaturationMonoid
