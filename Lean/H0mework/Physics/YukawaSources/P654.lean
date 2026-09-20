import Mathlib.Tactic
import H0mework.Physics.MixingSources.P653

/-!
# Proposition 654: Yukawa depths as one primitive-card closed stencil

P648 states the finite Yukawa producer in table language: primitive-card source
equations plus an endpoint-preserving SU(7) sector schedule force the selected
nine-depth table.  P584/P604 contain the stronger computational shape: those
nine integers are the nine values of one centered biquadratic stencil whose
coefficients are closed finite-card formulas.

This file exposes that shape as a producer certificate.  The output is not a
standalone list; it is the pointwise formula

`evalAt (primitiveCardYukawaDepthStencilCoefficientVector P) x y`

where `x` is the Poincare/generation coordinate and `y` is the SU(7)
endpoint-incidence sector coordinate.  Under the P606 primitive-card source
surface and endpoint preservation, that single formula produces the nine
documented depths

`[50, 346, 372, 489, 583, 682, 880, 908, 982]`.

Boundary: this is still the finite-card / endpoint-ordering producer.  It does
not derive the primitive-card source equations from smooth SU(7)-breaking
dynamics or a continuous consolidation flow.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Closed primitive-card stencil formula -/

/-- Closed primitive-card Yukawa depth formula at a matrix cell, with the
sector coordinate read from an arbitrary SU(7) endpoint-incidence schedule. -/
def yukawaPrimitiveCardEndpointClosedDepthFormulaAt
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) : Int :=
  let x :=
    poincareSlotDepthCoordinateZ
      (standardModelGenerationPoincareSlot g)
  let y := yukawaSectorInformationIncidenceTotalCoordinateZ (f s)
  YukawaDepthStencilCoefficientVector.evalAt
    (primitiveCardYukawaDepthStencilCoefficientVector P) x y

/-- The same closed formula read on a named Yukawa row. -/
def yukawaPrimitiveCardEndpointClosedDepthFormulaOf
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (y : YukawaParameter) : Int :=
  yukawaPrimitiveCardEndpointClosedDepthFormulaAt P f
    (yukawaMatrixCoordinates y).1 (yukawaMatrixCoordinates y).2

/-- THEOREM 1: the closed primitive-card formula is definitionally the
coefficient-vector / endpoint-schedule stencil already used by P594. -/
theorem yukawaPrimitiveCardEndpointClosedDepthFormulaAt_eq_coefficientVector
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (g : StandardModelFermionGeneration)
    (s : YukawaInteractionSector) :
    yukawaPrimitiveCardEndpointClosedDepthFormulaAt P f g s =
      coefficientVectorEndpointScheduleYukawaDepthStencilAt
        (primitiveCardYukawaDepthStencilCoefficientVector P) f g s := by
  rfl

/-- THEOREM 2: primitive-card source equations force the closed coefficient
vector to be P593's carrier-sourced vector. -/
theorem primitiveCardClosedCoefficientVector_eq_carrierSourced
    (P : YukawaCoefficientPrimitiveCardPacket)
    (hP : YukawaPrimitiveCardSourceEquations P) :
    primitiveCardYukawaDepthStencilCoefficientVector P =
      carrierSourcedYukawaDepthStencilCoefficientVector := by
  rw [eq_canonicalYukawaCoefficientPrimitiveCardPacket_of_sourceEquations P hP]
  exact canonicalPrimitiveCardYukawaDepthStencilCoefficientVector_eq_carrierSourced

/-- THEOREM 3: primitive-card source equations satisfy the coefficient-source
equations targeted by P594. -/
theorem primitiveCardClosedCoefficientVector_sourceEquations
    (P : YukawaCoefficientPrimitiveCardPacket)
    (hP : YukawaPrimitiveCardSourceEquations P) :
    YukawaCoefficientCarrierSourceEquations
      (primitiveCardYukawaDepthStencilCoefficientVector P) := by
  rw [primitiveCardClosedCoefficientVector_eq_carrierSourced P hP]
  exact carrierSourcedYukawaDepthStencilCoefficientVector_sourceEquations

/-- THEOREM 4: under the primitive-card source surface and endpoint
preservation, the one closed stencil formula reproduces each selected integer
Yukawa depth. -/
theorem yukawaPrimitiveCardEndpointClosedDepthFormulaOf_eq_selectedDepthZ
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (y : YukawaParameter) :
    yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f y =
      selectedYukawaIntegerDepthZ y := by
  exact
    coefficientVectorEndpointScheduleYukawaDepthStencilOf_eq_selectedDepthZ
      (primitiveCardYukawaDepthStencilCoefficientVector P)
      (primitiveCardClosedCoefficientVector_sourceEquations P hP)
      f hf y

/-- THEOREM 5: the same closed formula forces the documented mass-order list
of nine Yukawa depths. -/
theorem yukawaPrimitiveCardEndpointClosedDepthFormula_massOrder_eq
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .top).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .bottom).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .tau).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .charm).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .muon).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .strange).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .down).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .up).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  repeat rw [yukawaPrimitiveCardEndpointClosedDepthFormulaOf_eq_selectedDepthZ
    P f hP hf]
  rfl

/-- THEOREM 6: in the canonical packet/schedule, the primitive-card closed
formula is the P584 carrier-card stencil, pointwise on named Yukawa rows. -/
theorem canonicalPrimitiveCardClosedDepthFormulaOf_eq_carrierStencil
    (y : YukawaParameter) :
    yukawaPrimitiveCardEndpointClosedDepthFormulaOf
        canonicalYukawaCoefficientPrimitiveCardPacket
        yukawaSectorInformationIncidence y =
      yukawaDepthStencilOf y := by
  rw [yukawaPrimitiveCardEndpointClosedDepthFormulaOf_eq_selectedDepthZ
      canonicalYukawaCoefficientPrimitiveCardPacket
      yukawaSectorInformationIncidence
      canonicalYukawaCoefficientPrimitiveCardPacket_sourceEquations
      yukawaSectorInformationIncidence_endpointPreserving y,
    yukawaDepthStencilOf_eq_selectedDepthZ y]

/-- THEOREM 7: primitive-card source equations force the concrete closed
coefficient tuple used by the stencil formula. -/
theorem primitiveCardClosedCoefficientVector_tuple_forced
    (P : YukawaCoefficientPrimitiveCardPacket)
    (hP : YukawaPrimitiveCardSourceEquations P) :
    (primitiveCardYukawaDepthStencilCoefficientVector P).center = 682 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).generationSlope =
        267 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).sectorSlope = 47 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).generationCurvature =
        -69 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).sectorCurvature =
        -146 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).mixedTwist = -62 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).generationCurvatureSector =
        52 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).generationSectorCurvature =
        100 ∧
      (primitiveCardYukawaDepthStencilCoefficientVector P).bicurvature = 111 := by
  rw [primitiveCardClosedCoefficientVector_eq_carrierSourced P hP]
  exact carrierSourcedYukawaDepthStencilCoefficientVector_eq_tuple

/-! ## Certificate -/

/-- Compact certificate: the current finite Yukawa-depth producer is one closed
primitive-card stencil, not nine independent constants. -/
structure YukawaPrimitiveCardClosedStencilProducerCertificate where
  finite_depth :
    YukawaFiniteDepthProducerDebtClosureCertificate
  primitive_card :
    YukawaPrimitiveCardProducerReceipt
  carrier_stencil :
    YukawaDepthCarrierStencilReceipt
  closed_formula_definally_coefficient_vector :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (g : StandardModelFermionGeneration)
      (s : YukawaInteractionSector),
        yukawaPrimitiveCardEndpointClosedDepthFormulaAt P f g s =
          coefficientVectorEndpointScheduleYukawaDepthStencilAt
            (primitiveCardYukawaDepthStencilCoefficientVector P) f g s
  source_forces_coefficients :
    ∀ P : YukawaCoefficientPrimitiveCardPacket,
      YukawaPrimitiveCardSourceEquations P ->
        primitiveCardYukawaDepthStencilCoefficientVector P =
          carrierSourcedYukawaDepthStencilCoefficientVector
  source_forces_tuple :
    ∀ P : YukawaCoefficientPrimitiveCardPacket,
      YukawaPrimitiveCardSourceEquations P ->
        (primitiveCardYukawaDepthStencilCoefficientVector P).center = 682 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).generationSlope =
            267 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).sectorSlope =
            47 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).generationCurvature =
            -69 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).sectorCurvature =
            -146 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).mixedTwist =
            -62 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).generationCurvatureSector =
            52 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).generationSectorCurvature =
            100 ∧
          (primitiveCardYukawaDepthStencilCoefficientVector P).bicurvature =
            111
  pointwise_depths :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            ∀ y : YukawaParameter,
              yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f y =
                selectedYukawaIntegerDepthZ y
  mass_order :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .top).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .bottom).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .tau).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .charm).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .muon).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .strange).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .down).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .up).toNat
            , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f .electron).toNat
            ] =
              [50, 346, 372, 489, 583, 682, 880, 908, 982]
  canonical_equals_carrier_stencil :
    ∀ y : YukawaParameter,
      yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence y =
        yukawaDepthStencilOf y

/-- THEOREM 8: closed primitive-card stencil producer certificate. -/
theorem yukawaPrimitiveCardClosedStencilProducerCertificate :
    YukawaPrimitiveCardClosedStencilProducerCertificate where
  finite_depth := yukawaFiniteDepthProducerDebtClosureCertificate
  primitive_card := yukawaPrimitiveCardProducerReceipt
  carrier_stencil := yukawaDepthCarrierStencilReceipt
  closed_formula_definally_coefficient_vector :=
    yukawaPrimitiveCardEndpointClosedDepthFormulaAt_eq_coefficientVector
  source_forces_coefficients :=
    primitiveCardClosedCoefficientVector_eq_carrierSourced
  source_forces_tuple :=
    primitiveCardClosedCoefficientVector_tuple_forced
  pointwise_depths :=
    yukawaPrimitiveCardEndpointClosedDepthFormulaOf_eq_selectedDepthZ
  mass_order :=
    yukawaPrimitiveCardEndpointClosedDepthFormula_massOrder_eq
  canonical_equals_carrier_stencil :=
    canonicalPrimitiveCardClosedDepthFormulaOf_eq_carrierStencil

end StandardModelConstraint
end SaturationMonoid
