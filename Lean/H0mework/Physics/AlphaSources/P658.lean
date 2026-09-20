import Mathlib.Tactic
import H0mework.Physics.RepresentationSources.P464
import H0mework.Physics.YukawaSources.P657

/-!
# Proposition 658: alpha_s residual from trace weights and carrier data

P655 proves the exact alpha residual

`residual_inverse_needed = -89000/128511`

from the QCD/Poincare axis.  This file opens the QCD half of that axis one
more layer: `b0_QCD = 7` is not a naked integer input, but the value of the
standard one-loop trace-weight functional on the SU(7) block-incidence matter
carrier.

The producer chain certified here is:

`standard one-loop trace weights`
`+ SU(7) 3+2+1+1 block-incidence matter carrier`
`+ 4D Poincare slot carrier`
`-> axis 10`
`-> alpha gap 89/10000`
`-> inverse residual -89000/128511`.

Boundary: the universal one-loop weights themselves are still standard QFT
input; this file does not derive `11/3` from a heat-kernel/Feynman integral,
and it does not add smooth threshold / three-loop / Higgs-spectrum dynamics.
It removes the remaining *finite producer* opacity around `b0_QCD=7` inside
the alpha residual certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Trace-weighted QCD input -/

/-- THEOREM 1: the QCD block-incidence input is evaluated by the standard
one-loop trace weights. -/
theorem alphaStrongQCDInput_betaCoeff_traceWeighted :
    betaCoeff qcdBlockIncidenceOneLoopInput =
      applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput :=
  betaCoeff_eq_standardTraceOneLoopWeights qcdBlockIncidenceOneLoopInput

/-- THEOREM 2: the trace-weighted QCD block-incidence input evaluates to
`b0_QCD = 7`. -/
theorem alphaStrongQCDInput_traceWeighted_eq_seven :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput =
      (7 : ℚ) := by
  rw [(alphaStrongQCDInput_betaCoeff_traceWeighted).symm,
    qcd_b0_from_final_carrier_formula]

/-- THEOREM 3: the trace-weighted QCD value plus the 4D Poincare slot count
is the same primitive axis `10`. -/
theorem alphaStrongTraceWeightedQCDPoincareAxis_eq_ten :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ) =
        (10 : ℚ) := by
  rw [alphaStrongQCDInput_traceWeighted_eq_seven,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three]
  norm_num

/-- THEOREM 4: the trace-weighted QCD/Poincare axis is definitionally the
same axis used in the P655 closed alpha gap. -/
theorem alphaStrongQCDPoincareAxisBlockFormula_eq_traceWeighted :
    alphaStrongQCDPoincareAxisBlockFormula =
      let a : ℚ :=
        applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)
      ((((2 : ℚ) ^ 7 + (a - 1)) - ((7 : ℚ) ^ 2 - 1)) /
        (a ^ alphaStrongResidualResolutionExponent)) := by
  rw [alphaStrongQCDPoincareAxisBlockFormula,
    (alphaStrongQCDInput_betaCoeff_traceWeighted)]

/-- THEOREM 5: therefore the trace-weighted carrier presentation transports
to the exact inverse residual. -/
theorem alphaStrongTraceWeightedQCDPoincare_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongQCDPoincareClosedGap_inverseCorrection

/-! ## Certificate -/

/-- Compact certificate: the current `alpha_s` residual producer is sourced by
the standard trace weights, the SU(7) block-incidence QCD matter carrier, and
the 4D Poincare slot carrier before it reaches the closed residual formula. -/
structure AlphaStrongTraceWeightedResidualProducerCertificate where
  one_loop_weights :
    OneLoopCoefficientProvenanceReceipt
  qcd_carrier :
    QCDCarrierB0FinalReceipt
  qcd_trace_formula :
    betaCoeff qcdBlockIncidenceOneLoopInput =
      applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput
  qcd_trace_value :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput =
      (7 : ℚ)
  poincare_slots :
    AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 = 3
  trace_weighted_axis :
    applyTraceOneLoopWeights
        standardTraceOneLoopUniversalWeights
        qcdBlockIncidenceOneLoopInput +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ) =
        (10 : ℚ)
  p655_closed_gap :
    AlphaStrongQCDPoincareClosedGapProducerCertificate
  axis_formula_trace_weighted :
    alphaStrongQCDPoincareAxisBlockFormula =
      let a : ℚ :=
        applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)
      ((((2 : ℚ) ^ 7 + (a - 1)) - ((7 : ℚ) ^ 2 - 1)) /
        (a ^ alphaStrongResidualResolutionExponent))
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 6: trace-weighted alpha residual producer certificate. -/
def alphaStrongTraceWeightedResidualProducerCertificate :
    AlphaStrongTraceWeightedResidualProducerCertificate where
  one_loop_weights := oneLoopCoefficientProvenanceReceipt
  qcd_carrier := qcdCarrierB0FinalReceipt
  qcd_trace_formula := alphaStrongQCDInput_betaCoeff_traceWeighted
  qcd_trace_value := alphaStrongQCDInput_traceWeighted_eq_seven
  poincare_slots :=
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three
  trace_weighted_axis := alphaStrongTraceWeightedQCDPoincareAxis_eq_ten
  p655_closed_gap := alphaStrongQCDPoincareClosedGapProducerCertificate
  axis_formula_trace_weighted :=
    alphaStrongQCDPoincareAxisBlockFormula_eq_traceWeighted
  inverse_residual := alphaStrongTraceWeightedQCDPoincare_inverseCorrection

end StandardModelConstraint
end SaturationMonoid
