import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P658

/-!
# Proposition 659: trace-weighted shared-axis three-nail producer

P657 and P658 close two different producer debts:

* P657 compresses the Yukawa/CKM finite producer to a one-axis source law;
* P658 opens the alpha residual axis to standard one-loop trace weights plus
  the SU(7) block-incidence QCD carrier and the 4D Poincare slot carrier.

This file welds them together.  The same trace-weighted axis

`applyTraceOneLoopWeights standardTraceOneLoopUniversalWeights qcdInput
  + PoincareSlots_4D = 10`

is the canonical one-axis producer used by the Yukawa and CKM closed stencil.
Thus the current finite spine is one certificate, not three parallel
presentations:

* `alpha_s` inverse residual `-89000/128511`;
* Yukawa depth list `[50,346,372,489,583,682,880,908,982]`;
* CKM/Jarlskog typed factors `-226, -143, 562, 193` and depth sum `386`.

Boundary: this is still the finite shared-axis producer spine.  It does not
derive the universal one-loop weights, threshold corrections, full CKM matrix,
or smooth SU(7)-breaking/consolidation dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open InformationMatterProjection

/-! ## Shared trace-weighted axis -/

/-- THEOREM 1: the canonical primitive one-axis producer is the
trace-weighted QCD/Poincare axis. -/
theorem canonicalOneAxisPrimitiveSourceProducer_axis_eq_traceWeighted :
    canonicalOneAxisPrimitiveSourceProducer.axis =
      applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ) := by
  rw [canonicalOneAxisPrimitiveSourceProducer_axis_eq_ten,
    alphaStrongTraceWeightedQCDPoincareAxis_eq_ten]

/-- THEOREM 2: the canonical primitive-card packet satisfies the source law
for the trace-weighted shared axis. -/
theorem traceWeightedSharedAxis_canonicalYukawaSourceLaw :
    OneAxisYukawaPrimitiveCardSourceLaw
      canonicalOneAxisPrimitiveSourceProducer
      canonicalYukawaCoefficientPrimitiveCardPacket :=
  canonicalYukawaPrimitiveCardPacket_oneAxisSourceLaw
    canonicalOneAxisPrimitiveSourceProducer

/-- THEOREM 3: the same source law implies the primitive-card source equations
for the canonical packet. -/
theorem traceWeightedSharedAxis_canonicalYukawaSourceEquations :
    YukawaPrimitiveCardSourceEquations
      canonicalYukawaCoefficientPrimitiveCardPacket :=
  oneAxisYukawaPrimitiveCardSourceLaw_to_sourceEquations
    canonicalOneAxisPrimitiveSourceProducer
    canonicalYukawaCoefficientPrimitiveCardPacket
    traceWeightedSharedAxis_canonicalYukawaSourceLaw

/-! ## Three nail outputs from the shared axis -/

/-- THEOREM 4: the trace-weighted shared axis transports to the exact alpha
inverse residual. -/
theorem traceWeightedSharedAxis_alphaInverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongTraceWeightedQCDPoincare_inverseCorrection

/-- THEOREM 5: the canonical closed stencil on the shared axis produces the
documented Yukawa mass-order depth list. -/
theorem traceWeightedSharedAxis_yukawaMassOrder :
    [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .top).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .bottom).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .tau).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .charm).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .muon).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .strange).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .down).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .up).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  yukawaPrimitiveCardEndpointClosedDepthFormula_massOrder_eq
    canonicalYukawaCoefficientPrimitiveCardPacket
    yukawaSectorInformationIncidence
    traceWeightedSharedAxis_canonicalYukawaSourceEquations
    yukawaSectorInformationIncidence_endpointPreserving

/-- THEOREM 6: the canonical closed stencil on the shared axis produces the
typed CKM/Jarlskog four-product factors. -/
theorem traceWeightedSharedAxis_ckmFactors :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) .V_us =
        (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence) .V_cb =
          (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution
            (yukawaPrimitiveCardClosedDepthTableCandidate
              canonicalYukawaCoefficientPrimitiveCardPacket
              yukawaSectorInformationIncidence) .V_ub_conj =
            (562 : Int) ∧
          CKMJarlskogFactor.depthContribution
              (yukawaPrimitiveCardClosedDepthTableCandidate
                canonicalYukawaCoefficientPrimitiveCardPacket
                yukawaSectorInformationIncidence) .V_cs_conj =
              (193 : Int) := by
  exact
    ⟨closedStencilCKMJarlskogFactor_V_us_eq_neg226
        canonicalYukawaCoefficientPrimitiveCardPacket
        yukawaSectorInformationIncidence
        traceWeightedSharedAxis_canonicalYukawaSourceEquations
        yukawaSectorInformationIncidence_endpointPreserving,
      closedStencilCKMJarlskogFactor_V_cb_eq_neg143
        canonicalYukawaCoefficientPrimitiveCardPacket
        yukawaSectorInformationIncidence
        traceWeightedSharedAxis_canonicalYukawaSourceEquations
        yukawaSectorInformationIncidence_endpointPreserving,
      closedStencilCKMJarlskogFactor_V_ub_conj_eq_562
        canonicalYukawaCoefficientPrimitiveCardPacket
        yukawaSectorInformationIncidence
        traceWeightedSharedAxis_canonicalYukawaSourceEquations
        yukawaSectorInformationIncidence_endpointPreserving,
      closedStencilCKMJarlskogFactor_V_cs_conj_eq_193
        canonicalYukawaCoefficientPrimitiveCardPacket
        yukawaSectorInformationIncidence
        traceWeightedSharedAxis_canonicalYukawaSourceEquations
        yukawaSectorInformationIncidence_endpointPreserving⟩

/-- THEOREM 7: the shared-axis closed stencil has the normal form
`2*(n_s-n_c)`. -/
theorem traceWeightedSharedAxis_ckmNormalForm :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      2 *
        charmStrangeDepthGap
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence) :=
  closedStencilCKMJarlskogFourProduct_normalForm
    canonicalYukawaCoefficientPrimitiveCardPacket
    yukawaSectorInformationIncidence

/-- THEOREM 8: the shared-axis closed stencil gives CKM/Jarlskog depth sum
`386`. -/
theorem traceWeightedSharedAxis_ckmDepthSum :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      (ckmCPDepthSum : Int) :=
  closedStencilCKMJarlskogFourProductDepthSum_eq_386
    canonicalYukawaCoefficientPrimitiveCardPacket
    yukawaSectorInformationIncidence
    traceWeightedSharedAxis_canonicalYukawaSourceEquations
    yukawaSectorInformationIncidence_endpointPreserving

/-! ## Certificate -/

/-- Compact certificate: the current finite Standard-Model projection has one
trace-weighted shared-axis producer for alpha, Yukawa depths, and
CKM/Jarlskog phase depth. -/
structure TraceWeightedSharedAxisThreeNailProducerCertificate where
  alpha_trace_weighted :
    AlphaStrongTraceWeightedResidualProducerCertificate
  one_axis_yukawa :
    OneAxisYukawaDepthProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer
  shared_axis :
    canonicalOneAxisPrimitiveSourceProducer.axis =
      applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ)
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511)
  yukawa_mass_order :
    [ (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .top).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .bottom).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .tau).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .charm).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .muon).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .strange).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .down).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .up).toNat
    , (yukawaPrimitiveCardEndpointClosedDepthFormulaOf
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence .electron).toNat
    ] =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_factors :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) .V_us =
        (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence) .V_cb =
          (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution
            (yukawaPrimitiveCardClosedDepthTableCandidate
              canonicalYukawaCoefficientPrimitiveCardPacket
              yukawaSectorInformationIncidence) .V_ub_conj =
            (562 : Int) ∧
          CKMJarlskogFactor.depthContribution
              (yukawaPrimitiveCardClosedDepthTableCandidate
                canonicalYukawaCoefficientPrimitiveCardPacket
                yukawaSectorInformationIncidence) .V_cs_conj =
              (193 : Int)
  ckm_normal_form :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      2 *
        charmStrangeDepthGap
          (yukawaPrimitiveCardClosedDepthTableCandidate
            canonicalYukawaCoefficientPrimitiveCardPacket
            yukawaSectorInformationIncidence)
  ckm_depth_sum :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate
          canonicalYukawaCoefficientPrimitiveCardPacket
          yukawaSectorInformationIncidence) =
      (ckmCPDepthSum : Int)

/-- THEOREM 9: trace-weighted shared-axis three-nail producer certificate. -/
def traceWeightedSharedAxisThreeNailProducerCertificate :
    TraceWeightedSharedAxisThreeNailProducerCertificate where
  alpha_trace_weighted := alphaStrongTraceWeightedResidualProducerCertificate
  one_axis_yukawa := canonicalOneAxisYukawaDepthProducerCertificate
  shared_axis := canonicalOneAxisPrimitiveSourceProducer_axis_eq_traceWeighted
  alpha_inverse_residual := traceWeightedSharedAxis_alphaInverseResidual
  yukawa_mass_order := traceWeightedSharedAxis_yukawaMassOrder
  ckm_factors := traceWeightedSharedAxis_ckmFactors
  ckm_normal_form := traceWeightedSharedAxis_ckmNormalForm
  ckm_depth_sum := traceWeightedSharedAxis_ckmDepthSum

end StandardModelConstraint
end SaturationMonoid
