import H0mework.Physics.AlphaSources.P792

/-!
# Proposition 793: SU(7) Yukawa depth generator

P645 proves that the SU(7) primitive Yukawa-depth producer surface is a
singleton.  This file changes the proof shape in the same way as P792:
primitive data first, numerical output second.

The generator takes:

* a primitive-card packet, i.e. the finite representation/card data that
  produces the Yukawa coefficient stencil; and
* a sector schedule, i.e. the consolidation/interaction ordering read from
  the endpoint-preserving SU(7) sector incidence.

It returns the generated Yukawa depth table, its per-parameter depth function,
and the documented mass-order list.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Primitive data and generator -/

/-- Primitive SU(7) Yukawa-depth data: representation/card packet plus the
sector schedule that plays the consolidation-ordering role in the finite
carrier. -/
structure SU7YukawaDepthGeneratorData where
  input : YukawaProducerInputCandidate

/-- Build generator data from the primitive-card packet and sector schedule
that expose the representation/consolidation-ordering interface. -/
def su7YukawaDepthGeneratorDataOfPrimitive
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector ->
      InformationMatterProjection.InformationSlot) :
    SU7YukawaDepthGeneratorData where
  input :=
    { coefficients := primitiveCardYukawaDepthStencilCoefficientVector P
      schedule := f }

/-- Generator table: primitive SU(7) data produces a Yukawa depth table. -/
def su7YukawaDepthGeneratorTable
    (D : SU7YukawaDepthGeneratorData) :
    YukawaDepthTableCandidate :=
  D.input.depthTable

/-- Generator depth readout for a named Yukawa parameter. -/
def su7YukawaDepthGenerator
    (D : SU7YukawaDepthGeneratorData)
    (y : YukawaParameter) : Int :=
  (su7YukawaDepthGeneratorTable D).depth y

/-- Generator mass-order readout:
`top, bottom, tau, charm, muon, strange, down, up, electron`. -/
def su7YukawaDepthGeneratorMassOrder
    (D : SU7YukawaDepthGeneratorData) : List Nat :=
  (su7YukawaDepthGeneratorTable D).massOrder

/-- Direct carrier-grid Yukawa depth readout.

This is the no-extra-table face of the generator: the named depth is read
straight from the SU(7) coefficient carrier grid. -/
def su7YukawaDepthCarrierGridGenerator
    (y : YukawaParameter) : ℚ :=
  rationalGridDepthOf carrierCoefficientYukawaDepthGrid y

/-- Direct carrier-grid mass-order readout. -/
def su7YukawaDepthCarrierGridMassOrder : List ℚ :=
  rationalGridMassOrder carrierCoefficientYukawaDepthGrid

/-- Canonical SU(7) Yukawa-depth data read from the primitive-card packet and
the endpoint-preserving sector incidence. -/
def canonicalSU7YukawaDepthData :
    SU7YukawaDepthGeneratorData :=
  su7YukawaDepthGeneratorDataOfPrimitive
    canonicalYukawaCoefficientPrimitiveCardPacket
    yukawaSectorInformationIncidence

/-! ## Canonical output -/

/-- THEOREM 1: canonical generator data is exactly P604's primitive-card
producer input. -/
theorem canonicalSU7YukawaDepthData_toInput_eq_primitive :
    canonicalSU7YukawaDepthData.input =
      primitiveCardYukawaProducerInputCandidate := by
  unfold canonicalSU7YukawaDepthData su7YukawaDepthGeneratorDataOfPrimitive
    primitiveCardYukawaProducerInputCandidate
    canonicalPrimitiveCardYukawaDepthStencilCoefficientVector
  rfl

/-- THEOREM 2: the canonical generator table is the selected depth table. -/
theorem su7YukawaDepthGeneratorTable_canonical_eq_selected :
    su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData =
      selectedYukawaDepthTableCandidate := by
  unfold su7YukawaDepthGeneratorTable
  rw [canonicalSU7YukawaDepthData_toInput_eq_primitive]
  exact
    yukawaProducerInput_depthTable_eq_selected
      primitiveCardYukawaProducerInputCandidate
      primitiveCardYukawaProducerInputCandidate_surface

/-- THEOREM 3: the canonical generator outputs the documented nine-depth
mass-order list. -/
theorem su7YukawaDepthGeneratorMassOrder_canonical_eq :
    su7YukawaDepthGeneratorMassOrder canonicalSU7YukawaDepthData =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  unfold su7YukawaDepthGeneratorMassOrder
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected]
  exact selectedYukawaDepthTableCandidate_massOrder_eq

/-- THEOREM 3b: the direct carrier-grid generator outputs the documented
nine-depth mass-order list. -/
theorem su7YukawaDepthCarrierGridMassOrder_eq :
    su7YukawaDepthCarrierGridMassOrder =
      ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℚ) := by
  unfold su7YukawaDepthCarrierGridMassOrder
  exact carrierCoefficientYukawaDepthGrid_massOrder_eq

/-- THEOREM 4: canonical generator per-row depth normal form. -/
theorem su7YukawaDepthGenerator_canonical_namedDepths :
    su7YukawaDepthGenerator canonicalSU7YukawaDepthData .top = 50 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .bottom = 346 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .tau = 372 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .charm = 489 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .muon = 583 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .strange = 682 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .down = 880 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .up = 908 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .electron = 982 := by
  unfold su7YukawaDepthGenerator
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected]
  norm_num [selectedYukawaDepthTableCandidate,
    selectedYukawaIntegerDepthZ, selectedYukawaIntegerDepth]

/-- THEOREM 4b: the canonical generator's named-depth readout is the same
readout as the carrier coefficient grid, coordinate by coordinate.  This is
the finite bridge used by the CKM producer: CKM phases can be read from the
SU(7) coefficient carrier without treating the selected table as an
independent input. -/
theorem su7YukawaDepthGenerator_canonical_depth_eq_carrierGrid
    (y : YukawaParameter) :
    (su7YukawaDepthGenerator canonicalSU7YukawaDepthData y : ℚ) =
      su7YukawaDepthCarrierGridGenerator y := by
  unfold su7YukawaDepthGenerator
  unfold su7YukawaDepthCarrierGridGenerator
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected,
    carrierCoefficientYukawaDepthGrid_eq_selected]
  cases y <;>
    norm_num [selectedYukawaDepthTableCandidate, rationalGridDepthOf,
      selectedYukawaDepthGrid, selectedYukawaIntegerDepthZ,
      selectedYukawaIntegerDepth, yukawaMatrixCoordinates,
      yukawaMatrixParameter]

/-- THEOREM 5: the generator's canonical table produces the CKM/Jarlskog
depth sum `386`. -/
theorem su7YukawaDepthGenerator_canonical_ckmDepthSum :
    ckmDepthSum_fromYukawaDepthTable
        (su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData) =
      (ckmCPDepthSum : Int) := by
  rw [su7YukawaDepthGeneratorTable_canonical_eq_selected]
  exact selectedYukawaDepthTableCandidate_ckmDepthSum_eq_386

/-- THEOREM 5b: the canonical generator's CKM/Jarlskog depth sum is the same
finite readout as the carrier coefficient grid. -/
theorem su7YukawaDepthGenerator_canonical_ckmDepthSum_eq_carrierGrid :
    (ckmDepthSum_fromYukawaDepthTable
        (su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData) : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid := by
  rw [su7YukawaDepthGenerator_canonical_ckmDepthSum,
    carrierCoefficientYukawaDepthGrid_jarlskogDepthSum_eq_386]
  norm_num [ckmCPDepthSum]

/-! ## Bundled generator certificate -/

/-- Generator-centered certificate for the SU(7) Yukawa-depth producer. -/
structure SU7YukawaDepthGeneratorCertificate where
  input_eq_primitive :
    canonicalSU7YukawaDepthData.input =
      primitiveCardYukawaProducerInputCandidate
  table_eq_selected :
    su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData =
      selectedYukawaDepthTableCandidate
  mass_order :
    su7YukawaDepthGeneratorMassOrder canonicalSU7YukawaDepthData =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  named_depths :
    su7YukawaDepthGenerator canonicalSU7YukawaDepthData .top = 50 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .bottom = 346 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .tau = 372 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .charm = 489 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .muon = 583 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .strange = 682 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .down = 880 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .up = 908 ∧
      su7YukawaDepthGenerator canonicalSU7YukawaDepthData .electron = 982
  named_depths_from_carrier_grid :
    ∀ y : YukawaParameter,
      (su7YukawaDepthGenerator canonicalSU7YukawaDepthData y : ℚ) =
        su7YukawaDepthCarrierGridGenerator y
  mass_order_from_carrier_grid :
    su7YukawaDepthCarrierGridMassOrder =
      ([50, 346, 372, 489, 583, 682, 880, 908, 982] : List ℚ)
  ckm_depth_sum :
    ckmDepthSum_fromYukawaDepthTable
        (su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData) =
      (ckmCPDepthSum : Int)
  ckm_depth_sum_from_carrier_grid :
    (ckmDepthSum_fromYukawaDepthTable
        (su7YukawaDepthGeneratorTable canonicalSU7YukawaDepthData) : ℚ) =
      ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid
  primitive_surface :
    SU7PrimitiveYukawaDepthProducerCertificate

/-- THEOREM 6: canonical SU(7) Yukawa-depth generator certificate. -/
theorem su7YukawaDepthGeneratorCertificate :
    SU7YukawaDepthGeneratorCertificate where
  input_eq_primitive := canonicalSU7YukawaDepthData_toInput_eq_primitive
  table_eq_selected := su7YukawaDepthGeneratorTable_canonical_eq_selected
  mass_order := su7YukawaDepthGeneratorMassOrder_canonical_eq
  named_depths := su7YukawaDepthGenerator_canonical_namedDepths
  named_depths_from_carrier_grid :=
    su7YukawaDepthGenerator_canonical_depth_eq_carrierGrid
  mass_order_from_carrier_grid :=
    su7YukawaDepthCarrierGridMassOrder_eq
  ckm_depth_sum := su7YukawaDepthGenerator_canonical_ckmDepthSum
  ckm_depth_sum_from_carrier_grid :=
    su7YukawaDepthGenerator_canonical_ckmDepthSum_eq_carrierGrid
  primitive_surface := su7PrimitiveYukawaDepthProducerCertificate

end StandardModelConstraint
end SaturationMonoid
