import H0mework.Physics.JointSources.P632

/-!
# Proposition 633: primitive source producer for the one-axis law

P632 made the current strongest finite root reusable:

`OneAxisFiniteSourceLaw a := a = b0_QCD + PoincareSlots_4D`.

This file lowers that target one step further.  Instead of handing Lean a bare
axis `a`, a primitive producer must expose:

* a QCD one-loop input;
* a spacetime/Poincare dimension;
* an axis equation built from `betaCoeff(input) + pairingSlotCount(dimension)`;
* proofs that the input is the block-incidence QCD input and the dimension is
  four.

Lean then proves that every such producer inherits the full P632 receipt:
alpha_s residual `-89000/128511`, the selected Yukawa mass-order list, and
CKM/Jarlskog `386`.

Boundary: this still uses the existing P461 QCD carrier receipt and P281 finite
Poincare slot theorem.  It is a primitive-source producer normal form, not yet
the smooth SU(7) threshold / three-loop / Higgs-spectrum dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Primitive source producer object -/

/-- A primitive one-axis source producer.  The point is to carry the source
coordinates instead of supplying a naked finite axis. -/
structure OneAxisPrimitiveSourceProducer where
  qcdInput : RunningSigmaBeta.GaugeTraceOneLoopInput
  spacetimeDimension : ℕ
  axis : ℚ
  qcd_input_eq :
    qcdInput = RunningSigmaBeta.qcdBlockIncidenceOneLoopInput
  spacetime_dimension_eq : spacetimeDimension = 4
  axis_eq_source :
    axis =
      RunningSigmaBeta.betaCoeff qcdInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount
          spacetimeDimension : ℚ)

/-- The canonical primitive producer assembled from the existing QCD carrier
and 4D Poincare slot producers. -/
def canonicalOneAxisPrimitiveSourceProducer :
    OneAxisPrimitiveSourceProducer where
  qcdInput := RunningSigmaBeta.qcdBlockIncidenceOneLoopInput
  spacetimeDimension := 4
  axis :=
    RunningSigmaBeta.betaCoeff
      RunningSigmaBeta.qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)
  qcd_input_eq := rfl
  spacetime_dimension_eq := rfl
  axis_eq_source := rfl

/-! ## Every primitive producer induces the P632 source law -/

/-- THEOREM 1: a primitive source producer induces the P632 one-axis source
law. -/
theorem oneAxisPrimitiveSourceProducer_sourceLaw
    (P : OneAxisPrimitiveSourceProducer) :
    OneAxisFiniteSourceLaw P.axis := by
  rw [OneAxisFiniteSourceLaw, P.axis_eq_source, P.qcd_input_eq,
    P.spacetime_dimension_eq]

/-- THEOREM 2: every primitive source producer has axis `10`. -/
theorem oneAxisPrimitiveSourceProducer_axis_eq_ten
    (P : OneAxisPrimitiveSourceProducer) :
    P.axis = (10 : ℚ) :=
  oneAxisFiniteSourceLaw_eq_ten
    (oneAxisPrimitiveSourceProducer_sourceLaw P)

/-- THEOREM 3: the primitive source producer surface has unique axis value. -/
theorem oneAxisPrimitiveSourceProducer_axis_unique
    (P Q : OneAxisPrimitiveSourceProducer) :
    P.axis = Q.axis := by
  rw [oneAxisPrimitiveSourceProducer_axis_eq_ten P,
    oneAxisPrimitiveSourceProducer_axis_eq_ten Q]

/-- THEOREM 4: the canonical primitive producer has axis `10`. -/
theorem canonicalOneAxisPrimitiveSourceProducer_axis_eq_ten :
    canonicalOneAxisPrimitiveSourceProducer.axis = (10 : ℚ) :=
  oneAxisPrimitiveSourceProducer_axis_eq_ten
    canonicalOneAxisPrimitiveSourceProducer

/-! ## Three-nail consequences inherited from P632 -/

/-- THEOREM 5: primitive producers inherit the exact alpha_s inverse residual. -/
theorem oneAxisPrimitiveSourceProducer_alphaInverseResidual
    (P : OneAxisPrimitiveSourceProducer) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap P.axis) =
      -((89000 : ℚ) / 128511) :=
  oneAxisAlphaStrongInverseCorrection_eq_neg_of_sourceLaw
    (oneAxisPrimitiveSourceProducer_sourceLaw P)

/-- THEOREM 6: primitive producers inherit the selected Yukawa mass-order list.
-/
theorem oneAxisPrimitiveSourceProducer_yukawaMassOrder
    (P : OneAxisPrimitiveSourceProducer) :
    rationalGridMassOrder (gridOfStencil (oneAxisYukawaRationalStencil P.axis)) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  oneAxisYukawaMassOrder_eq_of_sourceLaw
    (oneAxisPrimitiveSourceProducer_sourceLaw P)

/-- THEOREM 7: primitive producers inherit CKM/Jarlskog depth sum `386`. -/
theorem oneAxisPrimitiveSourceProducer_ckmDepthSum
    (P : OneAxisPrimitiveSourceProducer) :
    2 * oneAxisCKMSectorGap P.axis = (386 : ℚ) :=
  oneAxisCKMDepthSum_eq_386_of_sourceLaw
    (oneAxisPrimitiveSourceProducer_sourceLaw P)

/-! ## Bundled primitive producer receipt -/

/-- Compact receipt: primitive source data is enough to recover the full P632
finite-root receipt. -/
structure OneAxisPrimitiveSourceProducerReceipt
    (P : OneAxisPrimitiveSourceProducer) where
  source_law : OneAxisFiniteSourceLaw P.axis
  p632_receipt : OneAxisFiniteSourceLawReceipt P.axis
  axis : P.axis = (10 : ℚ)
  axis_unique :
    ∀ Q : OneAxisPrimitiveSourceProducer, P.axis = Q.axis
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap P.axis) =
      -((89000 : ℚ) / 128511)
  yukawa_mass_order :
    rationalGridMassOrder (gridOfStencil (oneAxisYukawaRationalStencil P.axis)) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum : 2 * oneAxisCKMSectorGap P.axis = (386 : ℚ)

/-- THEOREM 8: receipt constructor for every primitive producer. -/
theorem oneAxisPrimitiveSourceProducerReceipt
    (P : OneAxisPrimitiveSourceProducer) :
    OneAxisPrimitiveSourceProducerReceipt P where
  source_law := oneAxisPrimitiveSourceProducer_sourceLaw P
  p632_receipt :=
    oneAxisFiniteSourceLawReceipt
      (oneAxisPrimitiveSourceProducer_sourceLaw P)
  axis := oneAxisPrimitiveSourceProducer_axis_eq_ten P
  axis_unique := oneAxisPrimitiveSourceProducer_axis_unique P
  alpha_inverse_residual :=
    oneAxisPrimitiveSourceProducer_alphaInverseResidual P
  yukawa_mass_order := oneAxisPrimitiveSourceProducer_yukawaMassOrder P
  ckm_depth_sum := oneAxisPrimitiveSourceProducer_ckmDepthSum P

/-- THEOREM 9: the canonical producer has the bundled receipt. -/
theorem canonicalOneAxisPrimitiveSourceProducerReceipt :
    OneAxisPrimitiveSourceProducerReceipt
      canonicalOneAxisPrimitiveSourceProducer :=
  oneAxisPrimitiveSourceProducerReceipt
    canonicalOneAxisPrimitiveSourceProducer

end StandardModelConstraint
end SaturationMonoid
