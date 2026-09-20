import Mathlib.Tactic
import H0mework.Physics.JointSources.P592

/-!
# Proposition 593: one carrier-sourced coefficient producer for the Yukawa stencil

P584 introduced the nine integer coefficients of the centered Yukawa depth
stencil.  P587/P588 showed that those coefficients are finite-difference
coordinates and routed the remaining local cards `9` and `17` to existing
finite carriers.  P589-P592 then routed the two axes through Poincare slots and
SU(7) endpoint signatures.

This file collects the coefficient layer into one producer object:

* a nine-field coefficient vector;
* a carrier-sourced vector using only the already proved finite carrier cards
  `137`, `48`, `128`, low-energy visible `9`, component support `17`, and the
  SU(7) fundamental numeral `7`;
* proof that this vector is exactly P584's coefficient vector and therefore
  feeds the selected nine Yukawa depths and CKM/Jarlskog depth sum `386`.

Boundary: this is a finite-cardinality coefficient producer.  It is not the
still-missing dynamical SU(7) breaking / consolidation-order derivation of why
this coefficient law, rather than another carrier law, is selected.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Coefficient vectors -/

/-- Integer coefficient vector for the centered biquadratic Yukawa depth
stencil. -/
@[ext]
structure YukawaDepthStencilCoefficientVector where
  center : Int
  generationSlope : Int
  sectorSlope : Int
  generationCurvature : Int
  sectorCurvature : Int
  mixedTwist : Int
  generationCurvatureSector : Int
  generationSectorCurvature : Int
  bicurvature : Int

/-- P584's coefficient vector, collected from its individual definitions. -/
def p584YukawaDepthStencilCoefficientVector :
    YukawaDepthStencilCoefficientVector where
  center := yukawaDepthStencilCenter
  generationSlope := yukawaDepthStencilGenerationSlope
  sectorSlope := yukawaDepthStencilSectorSlope
  generationCurvature := yukawaDepthStencilGenerationCurvature
  sectorCurvature := yukawaDepthStencilSectorCurvature
  mixedTwist := yukawaDepthStencilMixedTwist
  generationCurvatureSector := yukawaDepthStencilGenerationCurvatureSector
  generationSectorCurvature := yukawaDepthStencilGenerationSectorCurvature
  bicurvature := yukawaDepthStencilBicurvature

/-- Carrier-sourced coefficient producer.  This is the same law as P584, but
with the local `9` and `17` cards read through P588's carrier sources. -/
def carrierSourcedYukawaDepthStencilCoefficientVector :
    YukawaDepthStencilCoefficientVector where
  center := 5 * alphaEMIntegerDenominator ℤ - 3
  generationSlope := 2 * alphaEMIntegerDenominator ℤ - 7
  sectorSlope := su7GaugeFreedomDimension ℤ - 1
  generationCurvature := -((alphaEMIntegerDenominator ℤ + 1) / 2)
  sectorCurvature :=
    -(alphaEMIntegerDenominator ℤ + visibleGaugeCarrierCardFromLowEnergyZ)
  mixedTwist := -(su7GaugeFreedomDimension ℤ + 2 * (7 : Int))
  generationCurvatureSector := su7GaugeFreedomDimension ℤ + 4
  generationSectorCurvature :=
    (visibleGaugeCarrierCardFromLowEnergyZ + 1) ^ (2 : Nat)
  bicurvature :=
    sevenFacetInformationStateCount ℤ -
      informationMatterSupportCardFromComponentCarrierZ

/-! ## The sourced vector is exactly the P584 vector -/

/-- THEOREM 1: the carrier-sourced coefficient vector evaluates to the concrete
integer tuple used by the selected depth stencil. -/
theorem carrierSourcedYukawaDepthStencilCoefficientVector_eq_tuple :
    carrierSourcedYukawaDepthStencilCoefficientVector.center = 682 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationSlope = 267 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.sectorSlope = 47 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvature =
        -69 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.sectorCurvature =
        -146 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.mixedTwist = -62 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvatureSector =
        52 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationSectorCurvature =
        100 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.bicurvature = 111 := by
  simp [carrierSourcedYukawaDepthStencilCoefficientVector,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine,
    informationMatterSupportCardFromComponentCarrierZ_eq_seventeen,
    alphaEMIntegerDenominator, su7GaugeFreedomDimension,
    sevenFacetInformationStateCount]

/-- THEOREM 2: collecting P584's definitions gives the same concrete tuple. -/
theorem p584YukawaDepthStencilCoefficientVector_eq_tuple :
    p584YukawaDepthStencilCoefficientVector.center = 682 ∧
      p584YukawaDepthStencilCoefficientVector.generationSlope = 267 ∧
      p584YukawaDepthStencilCoefficientVector.sectorSlope = 47 ∧
      p584YukawaDepthStencilCoefficientVector.generationCurvature = -69 ∧
      p584YukawaDepthStencilCoefficientVector.sectorCurvature = -146 ∧
      p584YukawaDepthStencilCoefficientVector.mixedTwist = -62 ∧
      p584YukawaDepthStencilCoefficientVector.generationCurvatureSector = 52 ∧
      p584YukawaDepthStencilCoefficientVector.generationSectorCurvature = 100 ∧
      p584YukawaDepthStencilCoefficientVector.bicurvature = 111 := by
  simpa [p584YukawaDepthStencilCoefficientVector] using
    yukawaDepthStencilCoefficients_eq.2

/-- THEOREM 3: the carrier-sourced producer is exactly the P584 coefficient
vector. -/
theorem carrierSourcedYukawaDepthStencilCoefficientVector_eq_p584 :
    carrierSourcedYukawaDepthStencilCoefficientVector =
      p584YukawaDepthStencilCoefficientVector := by
  ext <;>
    simp [carrierSourcedYukawaDepthStencilCoefficientVector,
      p584YukawaDepthStencilCoefficientVector,
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

/-! ## Sourced coefficients feed the endpoint-invariant depth receipt -/

/-- THEOREM 4: the carrier-sourced coefficient producer feeds the endpoint
schedule invariant depth receipt from P592. -/
theorem carrierSourcedCoefficients_feed_endpointScheduleDepthReceipt :
    carrierSourcedYukawaDepthStencilCoefficientVector =
        p584YukawaDepthStencilCoefficientVector ∧
      EndpointScheduleSourcedYukawaDepthReceipt := by
  exact ⟨carrierSourcedYukawaDepthStencilCoefficientVector_eq_p584,
    endpointScheduleSourcedYukawaDepthReceipt⟩

/-- Compact receipt: the nine Yukawa stencil coefficients are collected into a
single carrier-sourced producer object, and that producer feeds the P592
endpoint-invariant depth/CKM receipt. -/
structure YukawaCoefficientCarrierProducerReceipt where
  carrier_tuple :
    carrierSourcedYukawaDepthStencilCoefficientVector.center = 682 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationSlope = 267 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.sectorSlope = 47 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvature =
        -69 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.sectorCurvature =
        -146 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.mixedTwist = -62 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationCurvatureSector =
        52 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.generationSectorCurvature =
        100 ∧
      carrierSourcedYukawaDepthStencilCoefficientVector.bicurvature = 111
  equals_p584 :
    carrierSourcedYukawaDepthStencilCoefficientVector =
      p584YukawaDepthStencilCoefficientVector
  endpoint_schedule_depth_receipt :
    EndpointScheduleSourcedYukawaDepthReceipt

/-- THEOREM 5: carrier-sourced coefficient producer receipt. -/
theorem yukawaCoefficientCarrierProducerReceipt :
    YukawaCoefficientCarrierProducerReceipt where
  carrier_tuple :=
    carrierSourcedYukawaDepthStencilCoefficientVector_eq_tuple
  equals_p584 :=
    carrierSourcedYukawaDepthStencilCoefficientVector_eq_p584
  endpoint_schedule_depth_receipt :=
    endpointScheduleSourcedYukawaDepthReceipt

end StandardModelConstraint
end SaturationMonoid
