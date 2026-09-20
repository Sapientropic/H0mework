import H0mework.Physics.MixingSources.P636
import H0mework.Physics.YukawaSources.P645

/-!
# Proposition 646: one primitive axis drives the three producer nails

P633/P636 already show that a primitive one-axis source producer

`axis = b0_QCD + PoincareSlots_4D`

forces the canonical rational Yukawa grid.  P645 upgrades the integer Yukawa
table to a producer surface.  This file welds those layers:

* every `OneAxisPrimitiveSourceProducer` has axis `10`;
* it gives the `alpha_s` inverse residual `-89000/128511`;
* its Yukawa rational grid is the same grid as the primitive-card face;
* the corresponding primitive-card depth table lies on the P645 SU(7)
  primitive depth-producer surface;
* hence the same upstream primitive axis forces the nine depth integers and
  the typed Jarlskog depth sum `386`.

Boundary: this is still finite one-axis producer closure.  It does not yet
construct the smooth SU(7)-breaking / three-loop RG / threshold / Higgs
dynamics that produce the primitive one-axis source fields.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## One-axis Yukawa face equals the primitive-card table face -/

/-- THEOREM 1: every primitive one-axis Yukawa rational stencil is the same
stencil as the primitive-card Yukawa stencil. -/
theorem oneAxisPrimitiveSourceYukawaRationalStencil_eq_primitiveCard
    (P : OneAxisPrimitiveSourceProducer) :
    oneAxisPrimitiveSourceYukawaRationalStencil P =
      primitiveCardYukawaRationalStencil := by
  rw [oneAxisPrimitiveSourceYukawaRationalStencil_eq_canonical P,
    primitiveCardYukawaRationalStencil_eq_canonical]

/-- THEOREM 2: every primitive one-axis Yukawa rational grid is the same grid
as the primitive-card Yukawa grid. -/
theorem oneAxisPrimitiveSourceYukawaRationalGrid_eq_primitiveCardGrid
    (P : OneAxisPrimitiveSourceProducer) :
    oneAxisPrimitiveSourceYukawaRationalGrid P =
      primitiveCardYukawaRationalGrid :=
  oneAxisPrimitiveSourceYukawaRationalGrid_eq_primitiveCard P

/-- THEOREM 3: the primitive-card table face lies on the P645 SU(7)
primitive depth-producer surface. -/
theorem primitiveCardYukawaDepthTable_su7PrimitiveProducer :
    SU7PrimitiveYukawaDepthProducerSurface
      primitiveCardYukawaProducerInputCandidate.depthTable := by
  rw [primitiveCardYukawaDepthTable_eq_selected]
  exact selectedYukawaDepthTableCandidate_su7PrimitiveProducer

/-- THEOREM 4: the primitive-card table face is the selected table. -/
theorem primitiveCardYukawaDepthTable_eq_selected_from_su7Surface :
    primitiveCardYukawaProducerInputCandidate.depthTable =
      selectedYukawaDepthTableCandidate :=
  eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer
    primitiveCardYukawaProducerInputCandidate.depthTable
    primitiveCardYukawaDepthTable_su7PrimitiveProducer

/-! ## Three-nail consequence from one primitive source -/

/-- THEOREM 5: a primitive one-axis producer forces the P645 named Yukawa
depth list through the SU(7) primitive producer surface. -/
theorem oneAxisPrimitiveSource_forces_yukawaDepths
    (_P : OneAxisPrimitiveSourceProducer) :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  rw [primitiveCardYukawaDepthTable_eq_selected_from_su7Surface]
  exact selectedYukawaDepthTableCandidate_massOrder_eq

/-- THEOREM 6: a primitive one-axis producer forces the selected typed
Jarlskog four-product depth sum `386`. -/
theorem oneAxisPrimitiveSource_forces_typedJarlskogDepthSum
    (_P : OneAxisPrimitiveSourceProducer) :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int) := by
  exact
    su7PrimitiveYukawaDepthProducerSurface_jarlskog_eq_386
      primitiveCardYukawaProducerInputCandidate.depthTable
      primitiveCardYukawaDepthTable_su7PrimitiveProducer

/-- THEOREM 7: a primitive one-axis producer also forces the exact
`alpha_s` inverse residual. -/
theorem oneAxisPrimitiveSource_forces_alphaInverseResidual
    (P : OneAxisPrimitiveSourceProducer) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap P.axis) =
      -((89000 : ℚ) / 128511) :=
  oneAxisPrimitiveSourceProducer_alphaInverseResidual P

/-! ## Bundled receipt -/

/-- Compact receipt: a single primitive one-axis producer carries the current
finite closure of all three main nails. -/
structure OneAxisPrimitiveSourceThreeNailProducerCertificate
    (P : OneAxisPrimitiveSourceProducer) where
  source_law : OneAxisFiniteSourceLaw P.axis
  axis : P.axis = (10 : ℚ)
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap P.axis) =
      -((89000 : ℚ) / 128511)
  one_axis_stencil_eq_primitive_card :
    oneAxisPrimitiveSourceYukawaRationalStencil P =
      primitiveCardYukawaRationalStencil
  one_axis_grid_eq_primitive_card :
    oneAxisPrimitiveSourceYukawaRationalGrid P =
      primitiveCardYukawaRationalGrid
  table_surface :
    SU7PrimitiveYukawaDepthProducerSurface
      primitiveCardYukawaProducerInputCandidate.depthTable
  table_eq_selected :
    primitiveCardYukawaProducerInputCandidate.depthTable =
      selectedYukawaDepthTableCandidate
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  typed_jarlskog_sum :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int)

/-- THEOREM 8: one-axis primitive-source certificate constructor. -/
theorem oneAxisPrimitiveSourceThreeNailProducerCertificate
    (P : OneAxisPrimitiveSourceProducer) :
    OneAxisPrimitiveSourceThreeNailProducerCertificate P where
  source_law := oneAxisPrimitiveSourceProducer_sourceLaw P
  axis := oneAxisPrimitiveSourceProducer_axis_eq_ten P
  alpha_inverse_residual :=
    oneAxisPrimitiveSource_forces_alphaInverseResidual P
  one_axis_stencil_eq_primitive_card :=
    oneAxisPrimitiveSourceYukawaRationalStencil_eq_primitiveCard P
  one_axis_grid_eq_primitive_card :=
    oneAxisPrimitiveSourceYukawaRationalGrid_eq_primitiveCardGrid P
  table_surface := primitiveCardYukawaDepthTable_su7PrimitiveProducer
  table_eq_selected :=
    primitiveCardYukawaDepthTable_eq_selected_from_su7Surface
  yukawa_depths := oneAxisPrimitiveSource_forces_yukawaDepths P
  typed_jarlskog_sum :=
    oneAxisPrimitiveSource_forces_typedJarlskogDepthSum P

/-- THEOREM 9: canonical current one-axis source carries the three-nail
certificate. -/
theorem canonicalOneAxisPrimitiveSourceThreeNailProducerCertificate :
    OneAxisPrimitiveSourceThreeNailProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer :=
  oneAxisPrimitiveSourceThreeNailProducerCertificate
    canonicalOneAxisPrimitiveSourceProducer

end StandardModelConstraint
end SaturationMonoid
