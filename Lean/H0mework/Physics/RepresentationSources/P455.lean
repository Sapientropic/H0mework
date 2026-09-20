/-
  Proposition 455: the one-loop b0 coefficient as a carrier formula.

  P451 proves the residual saturation law once a scalar `b0` is supplied.
  P453/P454 compute the Standard-Model table.  This file records the tighter
  interpretation: `b0` is not an adjustable external scalar.  It is the value
  of the standard Lie-algebraic one-loop coefficient function on the gauge
  factor and representation trace selected by the carrier.

  Boundary: the universal one-loop coefficient function is still the standard
  QFT/Lie-algebraic formula.  What is internal to the carrier is the choice of
  Lie algebra block and matter representation trace; once those are fixed,
  `b0` is forced.
-/

import H0mework.Physics.RepresentationSources.P454

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Carrier-selected representation traces -/

/-- The standard one-loop beta-coefficient function in trace form.  It is a
mathematical function of the Lie algebra datum `C_A` and the matter
representation traces, not a free parameter. -/
def betaCoeff (I : GaugeTraceOneLoopInput) : ℚ :=
  I.asymptoticB0

/-- The carrier-selected trace input for each Standard-Model gauge factor.

The entries are the coefficient-level projection of the `3+2+1+1` block
carrier (P286) together with the three 4D Poincare generation slots
(P416/P417):

* color: `C_A=3`, four color-fundamental Weyl slots per generation, no colored
  Higgs scalar;
* weak: `C_A=2`, four weak doublet slots per generation, one Higgs doublet;
* hypercharge: `C_A=0`, the usual SM hypercharge-square traces.
-/
def carrierTraceInput : StandardModelGaugeFactor -> GaugeTraceOneLoopInput
  | .colorSU3 =>
      { adjointCasimir := 3
        weylDynkinTrace :=
          (Fintype.card StandardModelFermionGeneration : ℚ) * (4 * (1 / 2))
        scalarDynkinTrace := 0 }
  | .weakSU2 =>
      { adjointCasimir := 2
        weylDynkinTrace :=
          (Fintype.card StandardModelFermionGeneration : ℚ) * (4 * (1 / 2))
        scalarDynkinTrace := 1 / 2 }
  | .hyperchargeU1 =>
      { adjointCasimir := 0
        weylDynkinTrace := 10
        scalarDynkinTrace := 1 / 2 }

/-- The final carrier formula: `b0 = beta_coeff(Lie_algebra, representation)`.
-/
def carrierB0 (G : StandardModelGaugeFactor) : ℚ :=
  betaCoeff (carrierTraceInput G)

/-- Three Poincare generation slots times four color-fundamental Weyl slots
per generation, with `T(fund)=1/2`, force the QCD Weyl trace to be `6`. -/
theorem qcd_weylDynkinTrace_from_poincare_slots :
    (Fintype.card StandardModelFermionGeneration : ℚ) * (4 * (1 / 2)) = 6 := by
  rw [standardModel_generation_count_three]
  norm_num

/-- The same three-slot count forces the weak Weyl trace to be `6`. -/
theorem weak_weylDynkinTrace_from_poincare_slots :
    (Fintype.card StandardModelFermionGeneration : ℚ) * (4 * (1 / 2)) = 6 := by
  exact qcd_weylDynkinTrace_from_poincare_slots

/-- QCD b0 from the carrier formula:
`b0 = betaCoeff(su(3), 3 generations × 4 fundamentals × T=1/2) = 7`. -/
theorem carrierB0_color :
    carrierB0 .colorSU3 = 7 := by
  norm_num [carrierB0, betaCoeff, carrierTraceInput,
    GaugeTraceOneLoopInput.asymptoticB0, standardModel_generation_count_three]

/-- Weak-sector b0 from the carrier formula:
`b0 = betaCoeff(su(2), 3 generations × 4 doublets × T=1/2, one Higgs) = 19/6`.
-/
theorem carrierB0_weak :
    carrierB0 .weakSU2 = 19 / 6 := by
  norm_num [carrierB0, betaCoeff, carrierTraceInput,
    GaugeTraceOneLoopInput.asymptoticB0, standardModel_generation_count_three]

/-- Hypercharge b0 from the same trace-form coefficient:
`b_asym = -41/6`, i.e. common SM convention `b_1 = 41/6`. -/
theorem carrierB0_hypercharge :
    carrierB0 .hyperchargeU1 = -(41 / 6) := by
  norm_num [carrierB0, betaCoeff, carrierTraceInput,
    GaugeTraceOneLoopInput.asymptoticB0]

/-- The carrier formula agrees with the P453 Standard-Model asymptotic table. -/
theorem carrierB0_eq_standardModelAsymptoticB0
    (G : StandardModelGaugeFactor) :
    carrierB0 G = standardModelAsymptoticB0 G := by
  cases G
  · rw [carrierB0_color, standardModelAsymptoticB0_color]
  · rw [carrierB0_weak, standardModelAsymptoticB0_weak]
  · rw [carrierB0_hypercharge, standardModelAsymptoticB0_hypercharge]

/-- QCD b0 is not an independent input once the color block and
Poincare-slot matter trace are fixed. -/
theorem qcd_b0_from_block_and_poincare_slots :
    betaCoeff
      { adjointCasimir := 3
        weylDynkinTrace :=
          (Fintype.card StandardModelFermionGeneration : ℚ) * (4 * (1 / 2))
        scalarDynkinTrace := 0 } = 7 := by
  norm_num [betaCoeff, GaugeTraceOneLoopInput.asymptoticB0,
    standardModel_generation_count_three]

/-- The running-sigma step can therefore be written directly with the carrier
formula, not with an independently supplied scalar. -/
theorem standardModelResidualSelfBump_delta_carrierFormula
    (G : StandardModelGaugeFactor) (σ : ℝ) :
    (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
      -(carrierB0 G : ℝ) * σ ^ 2 := by
  rw [standardModelResidualSelfBump_delta,
    carrierB0_eq_standardModelAsymptoticB0]

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
