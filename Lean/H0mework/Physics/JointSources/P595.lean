import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P594

/-!
# Proposition 595: selected depth closure is equivalent to source equations

P594 proved the forward direction:

`carrier-source equations + endpoint-preserving schedule -> selected depths`.

This file proves the finite reverse direction.  If an arbitrary coefficient
vector, evaluated along an endpoint-signature preserving SU(7) sector schedule,
reproduces all nine selected Yukawa depths, then the coefficient vector is
forced to be the carrier-sourced vector and therefore satisfies P594's source
equations.

Thus, at the finite coefficient layer, the source-equation interface is not
merely sufficient; it is equivalent to selected-depth grid closure.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Selected-depth closure forces the carrier-sourced vector -/

/-- THEOREM 1: reproducing all nine selected depths along an endpoint-preserving
schedule forces the coefficient vector to be P593's carrier-sourced vector. -/
theorem eq_carrierSourced_of_endpointSchedule_reproduces_selectedDepth
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hC : ∀ y : YukawaParameter,
      coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
        selectedYukawaIntegerDepthZ y) :
    C = carrierSourcedYukawaDepthStencilCoefficientVector := by
  rw [yukawaSectorEndpointSignaturePreservingSchedule_unique f hf] at hC
  rcases C with
    ⟨center, generationSlope, sectorSlope, generationCurvature,
      sectorCurvature, mixedTwist, generationCurvatureSector,
      generationSectorCurvature, bicurvature⟩
  have hup := hC .up
  have hdown := hC .down
  have helectron := hC .electron
  have hcharm := hC .charm
  have hstrange := hC .strange
  have hmuon := hC .muon
  have htop := hC .top
  have hbottom := hC .bottom
  have htau := hC .tau
  norm_num [coefficientVectorEndpointScheduleYukawaDepthStencilOf,
    coefficientVectorEndpointScheduleYukawaDepthStencilAt,
    YukawaDepthStencilCoefficientVector.evalAt, yukawaMatrixCoordinates,
    standardModelGenerationPoincareSlot, poincareSlotDepthCoordinateZ,
    poincareSlotOrbitIndexZ, yukawaSectorInformationIncidence,
    yukawaSectorInformationIncidenceTotalCoordinateZ,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth] at hup hdown helectron hcharm hstrange hmuon htop hbottom htau
  ext <;>
    simp [carrierSourcedYukawaDepthStencilCoefficientVector,
      visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
      informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
      alphaEMIntegerDenominator, su7GaugeFreedomDimension,
      sevenFacetInformationStateCount] <;>
    linarith

/-- THEOREM 2: reproducing all nine selected depths along an endpoint-preserving
schedule forces the P594 carrier-source equations. -/
theorem sourceEquations_of_endpointSchedule_reproduces_selectedDepth
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hC : ∀ y : YukawaParameter,
      coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
        selectedYukawaIntegerDepthZ y) :
    YukawaCoefficientCarrierSourceEquations C := by
  rw [eq_carrierSourced_of_endpointSchedule_reproduces_selectedDepth C f hf hC]
  exact carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations

/-! ## Equivalence form -/

/-- A coefficient vector closes the selected depth grid along an
endpoint-preserving schedule. -/
def EndpointScheduleSelectedDepthClosure
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot) : Prop :=
  YukawaSectorEndpointSignaturePreservingSchedule f ∧
    ∀ y : YukawaParameter,
      coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
        selectedYukawaIntegerDepthZ y

/-- THEOREM 3: for any endpoint-preserving schedule, selected-depth closure is
equivalent to the carrier-source equations. -/
theorem endpointScheduleSelectedDepthClosure_iff_sourceEquations
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    (∀ y : YukawaParameter,
      coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
        selectedYukawaIntegerDepthZ y) ↔
      YukawaCoefficientCarrierSourceEquations C := by
  constructor
  · intro h
    exact sourceEquations_of_endpointSchedule_reproduces_selectedDepth
      C f hf h
  · intro hsrc y
    exact coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
      C hsrc f hf y

/-- THEOREM 4: closure with its endpoint-preserving witness is equivalent to
the carrier-source equations plus the same endpoint witness. -/
theorem endpointScheduleSelectedDepthClosure_iff
    (C : YukawaDepthStencilCoefficientVector)
    (f : YukawaInteractionSector -> InformationSlot) :
    EndpointScheduleSelectedDepthClosure C f ↔
      YukawaSectorEndpointSignaturePreservingSchedule f ∧
        YukawaCoefficientCarrierSourceEquations C := by
  constructor
  · intro h
    exact ⟨h.1,
      sourceEquations_of_endpointSchedule_reproduces_selectedDepth
        C f h.1 h.2⟩
  · intro h
    exact ⟨h.1, fun y =>
      coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
        C h.2 f h.1 y⟩

/-! ## Bundled receipt -/

/-- Compact receipt: at the finite coefficient layer, P594's source-equation
interface is equivalent to selected-depth closure. -/
structure YukawaCoefficientSourceEquationsIffDepthClosureReceipt where
  depth_closure_forces_vector :
    ∀ C : YukawaDepthStencilCoefficientVector,
      ∀ f : YukawaInteractionSector -> InformationSlot,
        YukawaSectorEndpointSignaturePreservingSchedule f ->
          (∀ y : YukawaParameter,
            coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
              selectedYukawaIntegerDepthZ y) ->
            C = carrierSourcedYukawaDepthStencilCoefficientVector
  depth_closure_forces_source_equations :
    ∀ C : YukawaDepthStencilCoefficientVector,
      ∀ f : YukawaInteractionSector -> InformationSlot,
        YukawaSectorEndpointSignaturePreservingSchedule f ->
          (∀ y : YukawaParameter,
            coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
              selectedYukawaIntegerDepthZ y) ->
            YukawaCoefficientCarrierSourceEquations C
  source_equations_iff_depth_closure :
    ∀ C : YukawaDepthStencilCoefficientVector,
      ∀ f : YukawaInteractionSector -> InformationSlot,
        ∀ _ : YukawaSectorEndpointSignaturePreservingSchedule f,
          (∀ y : YukawaParameter,
            coefficientVectorEndpointScheduleYukawaDepthStencilOf C f y =
              selectedYukawaIntegerDepthZ y) ↔
            YukawaCoefficientCarrierSourceEquations C

/-- THEOREM 5: source-equations iff selected-depth-closure receipt. -/
theorem yukawaCoefficientSourceEquationsIffDepthClosureReceipt :
    YukawaCoefficientSourceEquationsIffDepthClosureReceipt where
  depth_closure_forces_vector :=
    eq_carrierSourced_of_endpointSchedule_reproduces_selectedDepth
  depth_closure_forces_source_equations :=
    sourceEquations_of_endpointSchedule_reproduces_selectedDepth
  source_equations_iff_depth_closure :=
    endpointScheduleSelectedDepthClosure_iff_sourceEquations

end StandardModelConstraint
end SaturationMonoid
