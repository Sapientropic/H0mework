/-
  Proposition 462: unified Standard-Model one-loop b0 carrier receipt.

  P461 packages the QCD/color case as an end-to-end carrier receipt.  This file
  removes the last color-only presentation artifact: the same `3+2+1+1`
  block-incidence carrier, the same three Poincare generation slots, and the
  same trace-form one-loop coefficient function compute all three Standard-
  Model gauge-factor coefficients.

  Boundary: as in P455/P461, the universal one-loop coefficient function is
  still standard Lie/QFT input.  The proved point is that the carrier fixes the
  Lie block and matter traces, hence the three rational coefficients and their
  residual self-bump running-sigma laws are not independent parameters.
-/

import H0mework.Physics.AlphaSources.P461

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Three-factor coefficient closure from the block-incidence carrier -/

/-- THEOREM 1: the block-incidence carrier computes the weak-sector
asymptotic coefficient `b0 = 19/6`. -/
theorem weak_b0_from_block_incidence_carrier :
    betaCoeff (incidenceCarrierTraceInput .weakSU2) = 19 / 6 := by
  rw [betaCoeff_incidenceCarrierTraceInput_eq_carrierB0, carrierB0_weak]

/-- THEOREM 2: the block-incidence carrier computes the hypercharge
asymptotic coefficient `b0 = -41/6` in the residual/asymptotic convention. -/
theorem hypercharge_b0_from_block_incidence_carrier :
    betaCoeff (incidenceCarrierTraceInput .hyperchargeU1) = -(41 / 6) := by
  rw [betaCoeff_incidenceCarrierTraceInput_eq_carrierB0,
    carrierB0_hypercharge]

/-- THEOREM 3: uniform coefficient statement for all three Standard-Model
gauge factors. -/
theorem standardModel_b0_from_block_incidence_carrier
    (G : StandardModelGaugeFactor) :
    betaCoeff (incidenceCarrierTraceInput G) = standardModelAsymptoticB0 G := by
  rw [betaCoeff_incidenceCarrierTraceInput_eq_carrierB0,
    carrierB0_eq_standardModelAsymptoticB0]

/-- THEOREM 4: the incidence-carrier coefficient agrees with the common
Standard-Model beta-table convention after negating the asymptotic
coefficient. -/
theorem standardModel_betaTableCoeff_from_block_incidence_carrier
    (G : StandardModelGaugeFactor) :
    -(betaCoeff (incidenceCarrierTraceInput G)) =
      standardModelBetaCoefficient G := by
  rw [standardModel_b0_from_block_incidence_carrier]
  cases G
  · rw [standardModelAsymptoticB0_color, standardModelBetaCoefficient_color]
  · rw [standardModelAsymptoticB0_weak, standardModelBetaCoefficient_weak]
  · rw [standardModelAsymptoticB0_hypercharge,
      standardModelBetaCoefficient_hypercharge]
    norm_num

/-! ## Three-factor running-sigma laws -/

/-- THEOREM 5: uniform running-sigma law with the block-incidence carrier
coefficient as the displayed `b0`. -/
theorem standardModelResidualSelfBump_delta_incidenceCarrierFormula
    (G : StandardModelGaugeFactor) (σ : ℝ) :
    (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
      -((betaCoeff (incidenceCarrierTraceInput G) : ℚ) : ℝ) * σ ^ 2 := by
  rw [standardModel_b0_from_block_incidence_carrier]
  exact standardModelResidualSelfBump_delta G σ

/-- THEOREM 6: color/QCD running-sigma law from the unified incidence carrier.
-/
theorem color_residualSelfBump_delta_from_unified_carrier
    (σ : ℝ) :
    (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
      -(7 : ℝ) * σ ^ 2 := by
  exact standardModelResidualSelfBump_delta_color σ

/-- THEOREM 7: weak-sector running-sigma law from the unified incidence
carrier. -/
theorem weak_residualSelfBump_delta_from_unified_carrier
    (σ : ℝ) :
    (standardModelOneLoopCarrier .weakSU2).residualSelfBumpStep σ - σ =
      -((19 : ℝ) / 6) * σ ^ 2 := by
  exact standardModelResidualSelfBump_delta_weak σ

/-- THEOREM 8: hypercharge running-sigma law from the unified incidence
carrier.  Since `b_asym = -41/6`, the residual-coordinate increment is
positive. -/
theorem hypercharge_residualSelfBump_delta_from_unified_carrier
    (σ : ℝ) :
    (standardModelOneLoopCarrier .hyperchargeU1).residualSelfBumpStep σ - σ =
      ((41 : ℝ) / 6) * σ ^ 2 := by
  exact standardModelResidualSelfBump_delta_hypercharge σ

/-! ## Bundled unified receipt -/

/-- The all-gauge-factor carrier receipt for the one-loop Standard-Model
running-sigma formula.

This extends P461's QCD receipt to the whole `SU(3) x SU(2) x U(1)` surface.
It intentionally records both sign conventions:

* `asymptotic_b0` is the coefficient in the residual law
  `delta sigma = -b0 sigma^2`;
* `beta_table_coeff` is the usual SM table convention, the negative of that
  asymptotic coefficient.
-/
structure StandardModelOneLoopCarrierFinalReceipt where
  qcd_receipt : QCDCarrierB0FinalReceipt
  block_dimension_sum :
    SU7CarrierBlock.fundamentalDimension .color +
      SU7CarrierBlock.fundamentalDimension .weak +
      SU7CarrierBlock.fundamentalDimension .positiveSinglet +
      SU7CarrierBlock.fundamentalDimension .negativeSinglet = 7
  incidence_orientation_unique :
    ∀ f : SU7BlockIncidence -> SU7GeneratedCarrierSlot,
      (∀ i : SU7BlockIncidence,
        generatedSlotEndpointSignature (f i) =
          SU7BlockIncidence.endpoints i) ->
        f = generatedSlotOfIncidence
  incidence_trace_reconstructs_multiplets :
    ∀ G : StandardModelGaugeFactor,
      incidenceCarrierTraceInput G = multipletCarrierTraceInput G
  incidence_trace_reconstructs_carrier :
    ∀ G : StandardModelGaugeFactor,
      incidenceCarrierTraceInput G = carrierTraceInput G
  asymptotic_b0 :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (incidenceCarrierTraceInput G) =
        standardModelAsymptoticB0 G
  beta_table_coeff :
    ∀ G : StandardModelGaugeFactor,
      -(betaCoeff (incidenceCarrierTraceInput G)) =
        standardModelBetaCoefficient G
  color_b0 :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = 7
  weak_b0 :
    betaCoeff (incidenceCarrierTraceInput .weakSU2) = 19 / 6
  hypercharge_b0 :
    betaCoeff (incidenceCarrierTraceInput .hyperchargeU1) = -(41 / 6)
  running_delta :
    ∀ G : StandardModelGaugeFactor, ∀ σ : ℝ,
      (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
        -((betaCoeff (incidenceCarrierTraceInput G) : ℚ) : ℝ) * σ ^ 2
  color_running_delta :
    ∀ σ : ℝ,
      (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
        -(7 : ℝ) * σ ^ 2
  weak_running_delta :
    ∀ σ : ℝ,
      (standardModelOneLoopCarrier .weakSU2).residualSelfBumpStep σ - σ =
        -((19 : ℝ) / 6) * σ ^ 2
  hypercharge_running_delta :
    ∀ σ : ℝ,
      (standardModelOneLoopCarrier .hyperchargeU1).residualSelfBumpStep σ - σ =
        ((41 : ℝ) / 6) * σ ^ 2

/-- THEOREM 9: the unified all-gauge-factor one-loop carrier receipt. -/
theorem standardModelOneLoopCarrierFinalReceipt :
    StandardModelOneLoopCarrierFinalReceipt where
  qcd_receipt := qcdCarrierB0FinalReceipt
  block_dimension_sum := SU7CarrierBlock.fundamentalDimension_sum
  incidence_orientation_unique :=
    su7IncidenceOrientationUniquenessCertificate.schedule_unique
  incidence_trace_reconstructs_multiplets :=
    incidenceCarrierTraceInput_eq_multipletCarrierTraceInput
  incidence_trace_reconstructs_carrier := by
    intro G
    rw [incidenceCarrierTraceInput_eq_multipletCarrierTraceInput,
      multipletCarrierTraceInput_eq_carrierTraceInput]
  asymptotic_b0 := standardModel_b0_from_block_incidence_carrier
  beta_table_coeff := standardModel_betaTableCoeff_from_block_incidence_carrier
  color_b0 := qcd_b0_from_block_incidence_carrier
  weak_b0 := weak_b0_from_block_incidence_carrier
  hypercharge_b0 := hypercharge_b0_from_block_incidence_carrier
  running_delta := standardModelResidualSelfBump_delta_incidenceCarrierFormula
  color_running_delta := color_residualSelfBump_delta_from_unified_carrier
  weak_running_delta := weak_residualSelfBump_delta_from_unified_carrier
  hypercharge_running_delta :=
    hypercharge_residualSelfBump_delta_from_unified_carrier

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
