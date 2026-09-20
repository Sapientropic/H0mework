import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P593

/-!
# Proposition 594: carrier-source equations force the Yukawa depth output

P593 collected the P584 Yukawa stencil coefficients into one carrier-sourced
producer vector.  This file removes the last dependence on that vector's name:
any coefficient vector satisfying the same carrier-source equations is forced
to be the P584/P593 vector, and therefore any endpoint-preserving sector
schedule fed through such a vector produces the selected nine Yukawa depths and
the CKM/Jarlskog depth sum `386`.

This is the finite interface that a later dynamical SU(7) breaking /
consolidation-order producer should target: prove the source equations, and
the already-certified finite depth/CKM output follows.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection
open InformationMatterProjection

namespace YukawaDepthStencilCoefficientVector

/-! ## Evaluation from an arbitrary coefficient vector -/

/-- Evaluate a coefficient vector at centered integer coordinates. -/
def evalAt (C : YukawaDepthStencilCoefficientVector) (x y : Int) : Int :=
  C.center +
    C.generationSlope * x +
    C.sectorSlope * y +
    C.generationCurvature * (x ^ (2 : Nat)) +
    C.sectorCurvature * (y ^ (2 : Nat)) +
    C.mixedTwist * x * y +
    C.generationCurvatureSector * (x ^ (2 : Nat)) * y +
    C.generationSectorCurvature * x * (y ^ (2 : Nat)) +
    C.bicurvature * (x ^ (2 : Nat)) * (y ^ (2 : Nat))

end YukawaDepthStencilCoefficientVector

/-! ## Source equations -/

/-- The carrier-source equations that select the finite coefficient law.

This predicate is intentionally the narrow target for the next, deeper
dynamical producer: once SU(7) breaking / consolidation ordering proves these
equations for a candidate coefficient vector, P594 supplies the rest of the
finite Yukawa-depth and CKM closure. -/
def YukawaCoefficientCarrierSourceEquations
    (C : YukawaDepthStencilCoefficientVector) : Prop :=
  C.center = 5 * alphaEMIntegerDenominator ℤ - 3 ∧
    C.generationSlope = 2 * alphaEMIntegerDenominator ℤ - 7 ∧
    C.sectorSlope = su7GaugeFreedomDimension ℤ - 1 ∧
    C.generationCurvature =
      -((alphaEMIntegerDenominator ℤ + 1) / 2) ∧
    C.sectorCurvature =
      -(alphaEMIntegerDenominator ℤ + visibleGaugeCarrierCardFromLowEnergyZ) ∧
    C.mixedTwist = -(su7GaugeFreedomDimension ℤ + 2 * (7 : Int)) ∧
    C.generationCurvatureSector = su7GaugeFreedomDimension ℤ + 4 ∧
    C.generationSectorCurvature =
      (visibleGaugeCarrierCardFromLowEnergyZ + 1) ^ (2 : Nat) ∧
    C.bicurvature =
      sevenFacetInformationStateCount ℤ -
        informationMatterSupportCardFromComponentCarrierZ

/-- THEOREM 1: P593's carrier-sourced vector satisfies the source equations. -/
theorem carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations :
    YukawaCoefficientCarrierSourceEquations
      carrierSourcedYukawaDepthStencilCoefficientVector := by
  simp [YukawaCoefficientCarrierSourceEquations,
    carrierSourcedYukawaDepthStencilCoefficientVector]

/-- THEOREM 2: any vector satisfying the carrier-source equations is exactly
P593's carrier-sourced vector. -/
theorem eq_carrierSourced_of_sourceEquations
    (C : YukawaDepthStencilCoefficientVector)
    (hC : YukawaCoefficientCarrierSourceEquations C) :
    C = carrierSourcedYukawaDepthStencilCoefficientVector := by
  rcases hC with
    ⟨hcenter, hgen, hsec, hgenCurv, hsecCurv, hmix,
      hgenCurvSec, hgenSecCurv, hbi⟩
  ext <;>
    simp [carrierSourcedYukawaDepthStencilCoefficientVector,
      hcenter, hgen, hsec, hgenCurv, hsecCurv, hmix,
      hgenCurvSec, hgenSecCurv, hbi]

/-! ## Any source-equation vector produces the same stencil -/

/-- Stencil evaluation from an arbitrary coefficient vector, with sector
coordinate read from an arbitrary SU(7) incidence schedule. -/
def coefficientVectorEndpointScheduleYukawaDepthStencilAt
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) : Int :=
  let x :=
    poincareSlotDepthCoordinateZ
      (standardModelGenerationPoincareSlot g)
  let y := yukawaSectorInformationIncidenceTotalCoordinateZ (f s)
  C.evalAt x y

/-- The same coefficient-vector stencil read on a named Yukawa row. -/
def coefficientVectorEndpointScheduleYukawaDepthStencilOf
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (y : YukawaParameter) : Int :=
  coefficientVectorEndpointScheduleYukawaDepthStencilAt C f
    (yukawaMatrixCoordinates y).1 (yukawaMatrixCoordinates y).2

/-- THEOREM 3: source equations make the coefficient-vector stencil equal to
P592's endpoint-schedule sourced stencil. -/
theorem coefficientVectorEndpointScheduleYukawaDepthStencilAt_eq_endpointSchedule
    (C : YukawaDepthStencilCoefficientVector)
    (hC : YukawaCoefficientCarrierSourceEquations C)
    (f : YukawaInteractionSector -> InformationSlot)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) :
    coefficientVectorEndpointScheduleYukawaDepthStencilAt C f g s =
      endpointScheduleSourcedYukawaDepthStencilAt f g s := by
  rw [eq_carrierSourced_of_sourceEquations C hC]
  simp [coefficientVectorEndpointScheduleYukawaDepthStencilAt,
    YukawaDepthStencilCoefficientVector.evalAt,
    endpointScheduleSourcedYukawaDepthStencilAt,
    carrierSourcedYukawaDepthStencilCoefficientVector]

/-- THEOREM 4: source equations plus endpoint preservation reproduce each
selected integer Yukawa depth. -/
theorem coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
    (C : YukawaDepthStencilCoefficientVector)
    (hC : YukawaCoefficientCarrierSourceEquations C)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (y : YukawaParameter) :
    coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
      selectedYukawaIntegerDepthZ y := by
  unfold coefficientVectorEndpointScheduleYukawaDepthStencilOf
  rw [coefficientVectorEndpointScheduleYukawaDepthStencilAt_eq_endpointSchedule
    C hC]
  exact endpointScheduleSourcedYukawaDepthStencilOf_eq_selectedDepthZ f hf y

/-- THEOREM 5: source equations plus endpoint preservation force the mass-order
depth list. -/
theorem coefficientVectorEndpointScheduleYukawaDepthStencil_massOrder_eq
    (C : YukawaDepthStencilCoefficientVector)
    (hC : YukawaCoefficientCarrierSourceEquations C)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    [ (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .top).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .tau).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .muon).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .down).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up).toNat
    , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  repeat rw [coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
    C hC f hf]
  rfl

/-- THEOREM 6: source equations plus endpoint preservation force the
CKM/Jarlskog depth sum `386`. -/
theorem ckmDepthSum_fromCoefficientVectorEndpointSchedule_eq_386
    (C : YukawaDepthStencilCoefficientVector)
    (hC : YukawaCoefficientCarrierSourceEquations C)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange -
        coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up) +
      (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom -
        coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm) +
      (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up -
        coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom) +
      (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange -
        coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm) =
        (ckmCPDepthSum : Int) := by
  repeat rw [coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
    C hC f hf]
  simpa [ckmDepthSum_fromYukawaDepths,
    ckmDepthDelta_us_fromYukawaDepths,
    ckmDepthDelta_cb_fromYukawaDepths,
    ckmDepthDelta_ub_conj_fromYukawaDepths,
    ckmDepthDelta_cs_conj_fromYukawaDepths] using
    ckmDepthSum_fromYukawaDepths_eq_386

/-! ## Bundled receipt -/

/-- Compact receipt: the finite coefficient source equations are a sufficient
and unique producer interface for the selected Yukawa depth table and the CKM
depth sum. -/
structure YukawaCoefficientSourceEquationReceipt where
  carrier_vector_satisfies :
    YukawaCoefficientCarrierSourceEquations
      carrierSourcedYukawaDepthStencilCoefficientVector
  unique_vector :
    ∀ C : YukawaDepthStencilCoefficientVector,
      YukawaCoefficientCarrierSourceEquations C ->
        C = carrierSourcedYukawaDepthStencilCoefficientVector
  reproduces_depths :
    ∀ C : YukawaDepthStencilCoefficientVector,
      YukawaCoefficientCarrierSourceEquations C ->
        ∀ f : YukawaInteractionSector -> InformationSlot,
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            ∀ y : YukawaParameter,
              coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
                selectedYukawaIntegerDepthZ y
  mass_order :
    ∀ C : YukawaDepthStencilCoefficientVector,
      YukawaCoefficientCarrierSourceEquations C ->
        ∀ f : YukawaInteractionSector -> InformationSlot,
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            [ (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .top).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .tau).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .muon).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .down).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up).toNat
            , (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .electron).toNat
            ] =
              [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ∀ C : YukawaDepthStencilCoefficientVector,
      YukawaCoefficientCarrierSourceEquations C ->
        ∀ f : YukawaInteractionSector -> InformationSlot,
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange -
                coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up) +
              (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom -
                coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm) +
              (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .up -
                coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .bottom) +
              (coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .strange -
                coefficientVectorEndpointScheduleYukawaDepthStencilOf C f .charm) =
                (ckmCPDepthSum : Int)

/-- THEOREM 7: source-equation producer receipt. -/
theorem yukawaCoefficientSourceEquationReceipt :
    YukawaCoefficientSourceEquationReceipt where
  carrier_vector_satisfies :=
    carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations
  unique_vector :=
    eq_carrierSourced_of_sourceEquations
  reproduces_depths :=
    coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
  mass_order :=
    coefficientVectorEndpointScheduleYukawaDepthStencil_massOrder_eq
  ckm_depth_sum :=
    ckmDepthSum_fromCoefficientVectorEndpointSchedule_eq_386

end StandardModelConstraint
end SaturationMonoid
