/-
  Proposition 464: provenance split for the one-loop rational constants.

  P462 proves that the `3+2+1+1` carrier computes all three Standard-Model
  one-loop coefficients once the standard one-loop coefficient function is
  available.  This file pins down the honest provenance split behind the
  small rational constants:

  * `11/3`, `2/3`, `1/3`, and `4/3` are universal one-loop QFT weights;
  * `C_A`, `T(R)`, the Weyl traces, and the scalar traces are the
    Lie/representation data selected by the carrier;
  * `1/2` is the standard fundamental-representation trace normalization used
    by the `SU(3)` and `SU(2)` carrier slots.

  Boundary: this does not derive the universal one-loop weights from a
  Feynman/heat-kernel calculation.  It proves that, after those universal
  weights are fixed, the carrier supplies the remaining Lie/representation
  input and therefore leaves no adjustable `b0` parameter.
-/

import H0mework.Physics.RepresentationSources.P462

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Universal one-loop weights versus carrier-selected invariants -/

/-- Universal trace-form one-loop weights.

The inputs multiplied by these weights are Lie/representation invariants:
`C_A`, `Σ Weyl T(R)`, and `Σ scalar T(R)`. -/
structure TraceOneLoopUniversalWeights where
  adjointGaugeBoson : ℚ
  weylFermionTrace : ℚ
  complexScalarTrace : ℚ

/-- The standard trace-form one-loop QFT weights:
`(11/3, 2/3, 1/3)`. -/
def standardTraceOneLoopUniversalWeights :
    TraceOneLoopUniversalWeights where
  adjointGaugeBoson := 11 / 3
  weylFermionTrace := 2 / 3
  complexScalarTrace := 1 / 3

/-- Apply universal trace-form weights to carrier-selected invariants. -/
def applyTraceOneLoopWeights
    (W : TraceOneLoopUniversalWeights)
    (I : GaugeTraceOneLoopInput) : ℚ :=
  W.adjointGaugeBoson * I.adjointCasimir -
    W.weylFermionTrace * I.weylDynkinTrace -
    W.complexScalarTrace * I.scalarDynkinTrace

/-- THEOREM 1: `betaCoeff` is exactly the standard universal trace weights
applied to the carrier-selected Lie/representation invariants. -/
theorem betaCoeff_eq_standardTraceOneLoopWeights
    (I : GaugeTraceOneLoopInput) :
    betaCoeff I =
      applyTraceOneLoopWeights standardTraceOneLoopUniversalWeights I := by
  rfl

/-- Universal Dirac-form one-loop weights.

The Dirac fermion coefficient `4/3` is twice the Weyl-trace coefficient `2/3`.
-/
structure DiracOneLoopUniversalWeights where
  adjointGaugeBoson : ℚ
  diracFermionTrace : ℚ
  complexScalarTrace : ℚ

/-- The standard Dirac-form one-loop QFT weights:
`(11/3, 4/3, 1/3)`. -/
def standardDiracOneLoopUniversalWeights :
    DiracOneLoopUniversalWeights where
  adjointGaugeBoson := 11 / 3
  diracFermionTrace := 4 / 3
  complexScalarTrace := 1 / 3

/-- Apply universal Dirac-form weights to a representation input. -/
def applyDiracOneLoopWeights
    (W : DiracOneLoopUniversalWeights)
    (I : NonabelianDiracOneLoopInput) : ℚ :=
  W.adjointGaugeBoson * I.adjointCasimir -
    W.diracFermionTrace * I.dynkinIndex * I.diracFermions -
    W.complexScalarTrace * I.dynkinIndex * I.complexScalars

/-- THEOREM 2: the Dirac-form coefficient function is exactly the standard
universal Dirac weights applied to the Lie/representation invariants. -/
theorem diracAsymptoticB0_eq_standardDiracOneLoopWeights
    (I : NonabelianDiracOneLoopInput) :
    I.asymptoticB0 =
      applyDiracOneLoopWeights standardDiracOneLoopUniversalWeights I := by
  rfl

/-- THEOREM 3: the Dirac fermion weight `4/3` is twice the Weyl trace weight
`2/3`. -/
theorem dirac_weight_is_two_weyl_weights :
    standardDiracOneLoopUniversalWeights.diracFermionTrace =
      2 * standardTraceOneLoopUniversalWeights.weylFermionTrace := by
  norm_num [standardDiracOneLoopUniversalWeights,
    standardTraceOneLoopUniversalWeights]

/-! ## The `1/2` trace normalization selected by the carrier -/

/-- Standard fundamental-representation trace normalization:
`Tr(TᵃTᵇ) = (1/2)δᵃᵇ`, recorded here only at coefficient level. -/
def suFundamentalDynkinIndex : ℚ := 1 / 2

/-- THEOREM 4: the coefficient-level fundamental Dynkin index is `1/2`. -/
theorem suFundamentalDynkinIndex_eq_half :
    suFundamentalDynkinIndex = 1 / 2 := by
  rfl

/-- THEOREM 5: the six-flavor QCD Dirac input uses the fundamental
normalization `T(fund)=1/2`. -/
theorem qcdSixFlavor_dynkinIndex_eq_suFundamental :
    qcdSixFlavorInput.dynkinIndex = suFundamentalDynkinIndex := by
  rfl

/-- THEOREM 6: the color carrier's Weyl trace is built from the three
generation slots, four color-fundamental Weyl slots per generation, and
`T(fund)=1/2`. -/
theorem color_carrier_weylTrace_from_suFundamental :
    (carrierTraceInput .colorSU3).weylDynkinTrace =
      (Fintype.card StandardModelFermionGeneration : ℚ) *
        (4 * suFundamentalDynkinIndex) := by
  rfl

/-- THEOREM 7: the weak carrier's Weyl trace is built from the three
generation slots, four weak-fundamental Weyl slots per generation, and
`T(fund)=1/2`. -/
theorem weak_carrier_weylTrace_from_suFundamental :
    (carrierTraceInput .weakSU2).weylDynkinTrace =
      (Fintype.card StandardModelFermionGeneration : ℚ) *
        (4 * suFundamentalDynkinIndex) := by
  rfl

/-- THEOREM 8: the weak Higgs scalar trace uses the same fundamental
normalization `T(fund)=1/2`. -/
theorem weak_carrier_scalarTrace_from_suFundamental :
    (carrierTraceInput .weakSU2).scalarDynkinTrace =
      suFundamentalDynkinIndex := by
  rfl

/-! ## Bundled provenance receipt -/

/-- The one-loop coefficient provenance receipt.

It keeps the two layers separate: universal QFT weights on one side,
carrier-selected Lie/representation invariants on the other. -/
structure OneLoopCoefficientProvenanceReceipt where
  trace_formula :
    ∀ I : GaugeTraceOneLoopInput,
      betaCoeff I =
        applyTraceOneLoopWeights standardTraceOneLoopUniversalWeights I
  dirac_formula :
    ∀ I : NonabelianDiracOneLoopInput,
      I.asymptoticB0 =
        applyDiracOneLoopWeights standardDiracOneLoopUniversalWeights I
  dirac_is_two_weyl :
    standardDiracOneLoopUniversalWeights.diracFermionTrace =
      2 * standardTraceOneLoopUniversalWeights.weylFermionTrace
  fundamental_index :
    suFundamentalDynkinIndex = 1 / 2
  qcd_uses_fundamental_index :
    qcdSixFlavorInput.dynkinIndex = suFundamentalDynkinIndex
  color_trace_uses_fundamental_index :
    (carrierTraceInput .colorSU3).weylDynkinTrace =
      (Fintype.card StandardModelFermionGeneration : ℚ) *
        (4 * suFundamentalDynkinIndex)
  weak_trace_uses_fundamental_index :
    (carrierTraceInput .weakSU2).weylDynkinTrace =
      (Fintype.card StandardModelFermionGeneration : ℚ) *
        (4 * suFundamentalDynkinIndex)
  weak_scalar_uses_fundamental_index :
    (carrierTraceInput .weakSU2).scalarDynkinTrace =
      suFundamentalDynkinIndex
  carrier_forces_all_b0 :
    StandardModelOneLoopCarrierFinalReceipt

/-- THEOREM 9: the coefficient provenance receipt. -/
theorem oneLoopCoefficientProvenanceReceipt :
    OneLoopCoefficientProvenanceReceipt where
  trace_formula := betaCoeff_eq_standardTraceOneLoopWeights
  dirac_formula := diracAsymptoticB0_eq_standardDiracOneLoopWeights
  dirac_is_two_weyl := dirac_weight_is_two_weyl_weights
  fundamental_index := suFundamentalDynkinIndex_eq_half
  qcd_uses_fundamental_index := qcdSixFlavor_dynkinIndex_eq_suFundamental
  color_trace_uses_fundamental_index :=
    color_carrier_weylTrace_from_suFundamental
  weak_trace_uses_fundamental_index :=
    weak_carrier_weylTrace_from_suFundamental
  weak_scalar_uses_fundamental_index :=
    weak_carrier_scalarTrace_from_suFundamental
  carrier_forces_all_b0 := standardModelOneLoopCarrierFinalReceipt

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
