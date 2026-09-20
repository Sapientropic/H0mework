import Mathlib.Tactic
import H0mework.Physics.MixingSources.P617
import H0mework.Physics.AlphaSources.P652

/-!
# Proposition 653: CKM/Jarlskog depth sum as a closed four-card formula

P617 shows that the CKM/Jarlskog phase-depth nail only needs the four-card
sector-axis packet `(alphaDenominator, visibleGauge, unifiedGaugeFreedom,
unit) = (137, 9, 48, 1)`.  P649 shows that the finite
primitive-card/endpoint-ordering producer forces the typed Jarlskog depth sum
`386`.

This file removes the last presentation layer around that `386`: it is the
closed four-card formula

`2 * ((48 - 1) - (-(137 + 9)))`.

That is, twice the sector-axis gap `(sectorSlope - sectorCurvature)`, with
`sectorSlope = SU7 freedom - unit` and
`sectorCurvature = -(alpha denominator + visible gauge)`.

Boundary: this is still the CKM phase-depth producer, not a full CKM matrix or
mixing-angle producer.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Closed four-card formula -/

/-- The CKM/Jarlskog depth sum read directly from the four primitive cards. -/
def ckmJarlskogFourCardClosedDepthSum : Int :=
  2 *
    (((su7GaugeFreedomDimension ℤ) - yukawaCoefficientUnitCardZ) -
      (-(alphaEMIntegerDenominator ℤ + visibleGaugeCarrierCardFromLowEnergyZ)))

/-- THEOREM 1: the closed four-card formula evaluates to `386`. -/
theorem ckmJarlskogFourCardClosedDepthSum_eq_386 :
    ckmJarlskogFourCardClosedDepthSum = (386 : Int) := by
  norm_num [ckmJarlskogFourCardClosedDepthSum, su7GaugeFreedomDimension,
    yukawaCoefficientUnitCardZ, alphaEMIntegerDenominator,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]

/-- THEOREM 2: the closed four-card formula is exactly the P617 canonical
minimal-sector packet's rational-grid Jarlskog output. -/
theorem ckmJarlskogFourCardClosedDepthSum_eq_canonicalSectorAxisGrid :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) := by
  rw [ckmJarlskogFourCardClosedDepthSum_eq_386,
    canonicalCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386]
  norm_num

/-- THEOREM 3: the closed formula is the same as the selected typed
Jarlskog depth sum constant. -/
theorem ckmCPDepthSum_eq_fourCardClosedDepthSum :
    (ckmCPDepthSum : Int) = ckmJarlskogFourCardClosedDepthSum := by
  rw [ckmJarlskogFourCardClosedDepthSum_eq_386]
  norm_num [ckmCPDepthSum]

/-- THEOREM 4: any finite primitive-card / endpoint-ordering producer that
forces the P649 typed Jarlskog sum forces the closed four-card formula. -/
theorem ckmJarlskogDepthSum_forced_eq_fourCardClosedFormula
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    ckmJarlskogFourProductDepthSum T =
      ckmJarlskogFourCardClosedDepthSum := by
  rw [ckmJarlskogDepthSum_forced_of_primitiveCards_and_endpointSchedule
    P f T hP hf hT]
  exact ckmCPDepthSum_eq_fourCardClosedDepthSum

/-- THEOREM 5: the four-card projection of any full Yukawa primitive-card
source packet produces the same closed formula in rational-grid coordinates.
-/
theorem ckmSectorAxisProjectionOfYukawaPacket_eq_fourCardClosedFormula
    (P : YukawaCoefficientPrimitiveCardPacket)
    (hP : YukawaPrimitiveCardSourceEquations P) :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            (ckmSectorAxisPacketOfYukawaPrimitiveCardPacket P))) =
      (ckmJarlskogFourCardClosedDepthSum : ℚ) := by
  rw [ckmSectorAxisProjectionOfYukawaPacket_jarlskogDepthSum_eq_386 P hP,
    ckmJarlskogFourCardClosedDepthSum_eq_386]
  norm_num

/-! ## Certificate -/

/-- Compact certificate: the current CKM/Jarlskog phase-depth producer is a
closed four-card formula, and the P649 primitive-card/endpoint producer
targets that same formula. -/
structure CKMJarlskogFourCardClosedFormulaProducerCertificate where
  sector_axis :
    CKMSectorAxisPrimitiveCardProducerReceipt
  finite_jarlskog :
    CKMFiniteJarlskogProducerDebtClosureCertificate
  root :
    CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate
  closed_formula :
    ckmJarlskogFourCardClosedDepthSum =
      2 *
        (((su7GaugeFreedomDimension ℤ) - yukawaCoefficientUnitCardZ) -
          (-(alphaEMIntegerDenominator ℤ +
              visibleGaugeCarrierCardFromLowEnergyZ)))
  closed_formula_value :
    ckmJarlskogFourCardClosedDepthSum = (386 : Int)
  selected_constant :
    (ckmCPDepthSum : Int) = ckmJarlskogFourCardClosedDepthSum
  canonical_sector_axis_grid :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket))
  forced_by_primitive_endpoint :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              ckmJarlskogFourProductDepthSum T =
                ckmJarlskogFourCardClosedDepthSum
  projected_full_yukawa_packet :
    ∀ P : YukawaCoefficientPrimitiveCardPacket,
      YukawaPrimitiveCardSourceEquations P ->
        ckmJarlskogDepthSumFromRationalGrid
            (gridOfStencil
              (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
                (ckmSectorAxisPacketOfYukawaPrimitiveCardPacket P))) =
          (ckmJarlskogFourCardClosedDepthSum : ℚ)

/-- THEOREM 6: closed four-card CKM/Jarlskog producer certificate. -/
def ckmJarlskogFourCardClosedFormulaProducerCertificate :
    CKMJarlskogFourCardClosedFormulaProducerCertificate where
  sector_axis := ckmSectorAxisPrimitiveCardProducerReceipt
  finite_jarlskog := ckmFiniteJarlskogProducerDebtClosureCertificate
  root := currentUnifiedEquationPrimeShadowThreeNailRootCertificate
  closed_formula := rfl
  closed_formula_value := ckmJarlskogFourCardClosedDepthSum_eq_386
  selected_constant := ckmCPDepthSum_eq_fourCardClosedDepthSum
  canonical_sector_axis_grid :=
    ckmJarlskogFourCardClosedDepthSum_eq_canonicalSectorAxisGrid
  forced_by_primitive_endpoint :=
    ckmJarlskogDepthSum_forced_eq_fourCardClosedFormula
  projected_full_yukawa_packet :=
    ckmSectorAxisProjectionOfYukawaPacket_eq_fourCardClosedFormula

end StandardModelConstraint
end SaturationMonoid
