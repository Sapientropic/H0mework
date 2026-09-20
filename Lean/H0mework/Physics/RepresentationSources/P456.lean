/-
  Proposition 456: Standard-Model matter traces from a finite Weyl-multiplet
  carrier.

  P455 states `b0 = betaCoeff(Lie_algebra, representation)` and records the
  carrier traces.  This file opens the representation side one more layer:
  the Weyl fermion traces are finite sums over the five Standard-Model chiral
  multiplets per generation, and the scalar traces are the Higgs doublet
  traces.  Thus the numbers `6`, `6`, and `10` are no longer opaque constants.

  Boundary: this is still representation bookkeeping.  It does not derive the
  Standard-Model representation list from first principles, prove anomaly
  cancellation, or derive the universal one-loop coefficient function.
-/

import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.RepresentationSources.P455

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Finite Standard-Model Weyl multiplet carrier -/

/-- The five chiral Weyl multiplets in one Standard-Model generation, written
in left-handed notation.  Conjugation signs are irrelevant for the quadratic
trace values used below. -/
inductive StandardModelWeylMultiplet where
  | quarkDoublet
  | upConjugate
  | downConjugate
  | leptonDoublet
  | electronConjugate
  deriving DecidableEq, Repr, FintypeViaProxy

namespace StandardModelWeylMultiplet

/-- QCD Dynkin trace per generation.  The quark doublet contributes two
color-fundamental Weyl slots; `uᶜ` and `dᶜ` contribute one each. -/
def colorDynkinTrace : StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 2 * (1 / 2)
  | .upConjugate => 1 / 2
  | .downConjugate => 1 / 2
  | .leptonDoublet => 0
  | .electronConjugate => 0

/-- Weak-isospin Dynkin trace per generation.  The quark doublet contributes
three weak doublets by color multiplicity, and the lepton doublet contributes
one. -/
def weakDynkinTrace : StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 3 * (1 / 2)
  | .upConjugate => 0
  | .downConjugate => 0
  | .leptonDoublet => 1 / 2
  | .electronConjugate => 0

/-- Hypercharge-square trace per generation in the usual SM normalization:

`Q: 6*(1/6)^2`, `uᶜ: 3*(2/3)^2`, `dᶜ: 3*(1/3)^2`,
`L: 2*(1/2)^2`, `eᶜ: 1`. -/
def hyperchargeSquareTrace : StandardModelWeylMultiplet -> ℚ
  | .quarkDoublet => 6 * (1 / 6) ^ 2
  | .upConjugate => 3 * (2 / 3) ^ 2
  | .downConjugate => 3 * (1 / 3) ^ 2
  | .leptonDoublet => 2 * (1 / 2) ^ 2
  | .electronConjugate => 1

/-- Explicit finite trace over the five one-generation Weyl multiplets. -/
def generationTrace (trace : StandardModelWeylMultiplet -> ℚ) : ℚ :=
  trace .quarkDoublet +
    trace .upConjugate +
    trace .downConjugate +
    trace .leptonDoublet +
    trace .electronConjugate

/-- Per-generation QCD trace: `2`. -/
theorem colorDynkinTrace_sum :
    generationTrace colorDynkinTrace = 2 := by
  norm_num [generationTrace, colorDynkinTrace]

/-- Per-generation weak trace: `2`. -/
theorem weakDynkinTrace_sum :
    generationTrace weakDynkinTrace = 2 := by
  norm_num [generationTrace, weakDynkinTrace]

/-- Per-generation hypercharge-square trace: `10/3`. -/
theorem hyperchargeSquareTrace_sum :
    generationTrace hyperchargeSquareTrace = 10 / 3 := by
  norm_num [generationTrace, hyperchargeSquareTrace]

end StandardModelWeylMultiplet

/-! ## Three-generation and Higgs traces -/

/-- Total Weyl trace selected by the three Poincare generation slots. -/
def totalWeylTrace
    (tracePerGeneration : StandardModelWeylMultiplet -> ℚ) : ℚ :=
  (Fintype.card StandardModelFermionGeneration : ℚ) *
    StandardModelWeylMultiplet.generationTrace tracePerGeneration

/-- QCD Weyl trace from finite multiplets and three Poincare slots: `6`. -/
theorem total_colorWeylTrace :
    totalWeylTrace StandardModelWeylMultiplet.colorDynkinTrace = 6 := by
  rw [totalWeylTrace, StandardModelWeylMultiplet.colorDynkinTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- Weak Weyl trace from finite multiplets and three Poincare slots: `6`. -/
theorem total_weakWeylTrace :
    totalWeylTrace StandardModelWeylMultiplet.weakDynkinTrace = 6 := by
  rw [totalWeylTrace, StandardModelWeylMultiplet.weakDynkinTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- Hypercharge Weyl trace from finite multiplets and three Poincare slots:
`10`. -/
theorem total_hyperchargeWeylTrace :
    totalWeylTrace StandardModelWeylMultiplet.hyperchargeSquareTrace = 10 := by
  rw [totalWeylTrace, StandardModelWeylMultiplet.hyperchargeSquareTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- The Higgs scalar trace for each gauge factor.  It is a weak doublet with
hypercharge-square trace `2*(1/2)^2 = 1/2` and no color charge. -/
def higgsScalarTrace : StandardModelGaugeFactor -> ℚ
  | .colorSU3 => 0
  | .weakSU2 => 1 / 2
  | .hyperchargeU1 => 2 * (1 / 2) ^ 2

theorem higgsScalarTrace_color :
    higgsScalarTrace .colorSU3 = 0 := rfl

theorem higgsScalarTrace_weak :
    higgsScalarTrace .weakSU2 = 1 / 2 := rfl

theorem higgsScalarTrace_hypercharge :
    higgsScalarTrace .hyperchargeU1 = 1 / 2 := by
  norm_num [higgsScalarTrace]

/-- Matter trace input computed from the finite Weyl multiplet carrier and
the Higgs scalar carrier. -/
def multipletCarrierTraceInput : StandardModelGaugeFactor -> GaugeTraceOneLoopInput
  | .colorSU3 =>
      { adjointCasimir := 3
        weylDynkinTrace := totalWeylTrace StandardModelWeylMultiplet.colorDynkinTrace
        scalarDynkinTrace := higgsScalarTrace .colorSU3 }
  | .weakSU2 =>
      { adjointCasimir := 2
        weylDynkinTrace := totalWeylTrace StandardModelWeylMultiplet.weakDynkinTrace
        scalarDynkinTrace := higgsScalarTrace .weakSU2 }
  | .hyperchargeU1 =>
      { adjointCasimir := 0
        weylDynkinTrace :=
          totalWeylTrace StandardModelWeylMultiplet.hyperchargeSquareTrace
        scalarDynkinTrace := higgsScalarTrace .hyperchargeU1 }

/-- The finite multiplet carrier reconstructs P455's carrier trace input. -/
theorem multipletCarrierTraceInput_eq_carrierTraceInput
    (G : StandardModelGaugeFactor) :
    multipletCarrierTraceInput G = carrierTraceInput G := by
  cases G
  · rw [multipletCarrierTraceInput, carrierTraceInput,
      total_colorWeylTrace, qcd_weylDynkinTrace_from_poincare_slots]
    simp [higgsScalarTrace]
  · rw [multipletCarrierTraceInput, carrierTraceInput,
      total_weakWeylTrace, weak_weylDynkinTrace_from_poincare_slots]
    simp [higgsScalarTrace]
  · simp [multipletCarrierTraceInput, carrierTraceInput,
      total_hyperchargeWeylTrace, higgsScalarTrace_hypercharge]

/-- `b0` computed from the finite multiplet carrier equals P455's carrier
formula. -/
theorem betaCoeff_multipletCarrierTraceInput_eq_carrierB0
    (G : StandardModelGaugeFactor) :
    betaCoeff (multipletCarrierTraceInput G) = carrierB0 G := by
  rw [multipletCarrierTraceInput_eq_carrierTraceInput]
  rfl

/-- QCD b0 from explicit one-generation multiplets, three Poincare slots, and
the color `SU(3)` block. -/
theorem qcd_b0_from_weyl_multiplets_and_poincare_slots :
    betaCoeff (multipletCarrierTraceInput .colorSU3) = 7 := by
  rw [betaCoeff_multipletCarrierTraceInput_eq_carrierB0, carrierB0_color]

/-- Weak-sector b0 from explicit one-generation multiplets, three Poincare
slots, and the weak `SU(2)` block. -/
theorem weak_b0_from_weyl_multiplets_and_poincare_slots :
    betaCoeff (multipletCarrierTraceInput .weakSU2) = 19 / 6 := by
  rw [betaCoeff_multipletCarrierTraceInput_eq_carrierB0, carrierB0_weak]

/-- Hypercharge b0 from explicit one-generation multiplets, three Poincare
slots, and the Higgs scalar trace. -/
theorem hypercharge_b0_from_weyl_multiplets_and_poincare_slots :
    betaCoeff (multipletCarrierTraceInput .hyperchargeU1) = -(41 / 6) := by
  rw [betaCoeff_multipletCarrierTraceInput_eq_carrierB0, carrierB0_hypercharge]

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
