import H0mework.Physics.AlphaSpectrum.P791

/-!
# Proposition 792: SU(7) alpha_s four-source generator

P785/P789/P791 computed the four alpha_s residual sources.  This file changes
the shape of the proof: instead of adding another target-number receipt, it
defines a source-level generator and its bundled-data encoding

`SU7BreakingData -> AlphaStrongResidualSource -> ℚ`.

The source-level generator has type

`AlphaStrongResidualSource -> ℚ`.

It calls the four physical source formulas directly: SU(7)-breaking card
source, threshold mismatch, RG mismatch, and Higgs/extra-spectrum mismatch.
The bundled-data generator is then proved to be only an encoding of that source
generator, not a target-shaped record readout.

The canonical SU(7) primitive data then computes the already bottomed
four-source vector:

`{su7Breaking := 89/10000, threshold := 0, threeLoopRG := 0,
  higgsExtraRepresentation := 0}`.

That makes the alpha_s producer a function out of primitive SU(7) data, not a
post-hoc equality to the displayed residual.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

/-! ## Primitive data and generator -/

/-- Primitive SU(7) data sufficient to generate the four alpha_s residual
source coordinates.

The fields are deliberately numerical carrier fields, not proof fields:
the generator below computes from them. -/
structure SU7BreakingData where
  alphaEMDenominator : ℚ
  su7GaugeFreedom : ℚ
  standardModelColorSlope : ℚ
  incidenceColorSlope : ℚ
  qcdBlockColorSlope : ℚ
  incidenceSlotCount : ℚ
  generatedSlotCount : ℚ
  resolutionAxis : ℚ
  resolutionExponent : Nat

/-- The denominator scale used by the four-source alpha_s generator. -/
def SU7BreakingData.resolutionDenominator (D : SU7BreakingData) : ℚ :=
  D.resolutionAxis ^ D.resolutionExponent

/-- The requested generator:

`SU7 primitive data -> alpha_s four-source vector`.

The four coordinates are SU(7) breaking, threshold mismatch, RG mismatch, and
Higgs/extra-representation mismatch. -/
def su7AlphaStrongFourSourceGenerator
    (D : SU7BreakingData) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      (D.alphaEMDenominator - D.su7GaugeFreedom) /
        D.resolutionDenominator
  | .threshold =>
      (D.standardModelColorSlope - D.incidenceColorSlope) /
        D.resolutionDenominator
  | .threeLoopRG =>
      (D.qcdBlockColorSlope - D.incidenceColorSlope) /
        D.resolutionDenominator
  | .higgsExtraRepresentation =>
      (D.incidenceSlotCount - D.generatedSlotCount) /
        D.resolutionDenominator

/-- The canonical SU(7) primitive data read from the existing block-incidence,
Poincare-axis, and one-loop carrier definitions. -/
def canonicalSU7Data : SU7BreakingData where
  alphaEMDenominator :=
    alphaStrongQCDPoincareStructuralAlphaEMDenominator
  su7GaugeFreedom :=
    su7GaugeFreedomDimension ℚ
  standardModelColorSlope :=
    standardModelAsymptoticB0 .colorSU3
  incidenceColorSlope :=
    betaCoeff (incidenceCarrierTraceInput .colorSU3)
  qcdBlockColorSlope :=
    betaCoeff qcdBlockIncidenceOneLoopInput
  incidenceSlotCount :=
    (Fintype.card SU7BlockIncidence : ℚ)
  generatedSlotCount :=
    (Fintype.card SU7GeneratedCarrierSlot : ℚ)
  resolutionAxis :=
    alphaStrongQCDPoincareResolutionAxis
  resolutionExponent :=
    alphaStrongResidualResolutionExponent

/-! ## Source-level primitive generator -/

/-- The source-level four-source generator.

Unlike `su7AlphaStrongFourSourceGenerator canonicalSU7Data`, this is not a
projection out of a bundled data record.  Each coordinate calls the structural
producer for that physical source:

* `SU(7)` breaking: the card-source gap `(2^7 + 9 - 48) / 10^4`;
* threshold: the Standard-Model/incidence color-slope mismatch;
* RG: the QCD-block/incidence color-slope mismatch;
* Higgs/extra spectrum: the incidence/generated-slot count mismatch. -/
def su7AlphaStrongFourSourcePrimitiveGenerator :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking => alphaStrongSU7BreakingCardSourceGap
  | .threshold => alphaStrongThresholdMismatchSourceGap
  | .threeLoopRG => alphaStrongThreeLoopRGMismatchSourceGap
  | .higgsExtraRepresentation =>
      alphaStrongHiggsExtraSpectrumMismatchSourceGap

/-- THEOREM 1a: the source-level generator is exactly the independent
four-source contribution function. -/
theorem su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent :
    su7AlphaStrongFourSourcePrimitiveGenerator =
      alphaStrongFourSourceIndependentContribution := by
  funext s
  cases s
  · exact alphaStrongFourSource_su7Breaking_eq_cardSourceGap.symm
  · rfl
  · rfl
  · rfl

/-- THEOREM 1c: the source-level generator has the requested four-source
normal form `{89/10000, 0, 0, 0}`. -/
theorem su7AlphaStrongFourSourcePrimitiveGenerator_normalForm :
    su7AlphaStrongFourSourcePrimitiveGenerator .su7Breaking =
        (89 : ℚ) / 10000 ∧
      su7AlphaStrongFourSourcePrimitiveGenerator .threshold = 0 ∧
        su7AlphaStrongFourSourcePrimitiveGenerator .threeLoopRG = 0 ∧
          su7AlphaStrongFourSourcePrimitiveGenerator
              .higgsExtraRepresentation = 0 := by
  rw [su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent]
  exact alphaStrongFourSourceIndependentContribution_bottomedNormalForm

/-- THEOREM 1d: the source-level generator sums to the displayed alpha-level
gap. -/
theorem su7AlphaStrongFourSourcePrimitiveGenerator_sum_eq_gap :
    (∑ s : AlphaStrongResidualSource,
        su7AlphaStrongFourSourcePrimitiveGenerator s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent]
  exact alphaStrongFourSourceIndependentContribution_bottomedSum_eq_gap

/-- THEOREM 1e: the source-level generator transports to the exact inverse
residual `-89000/128511`. -/
theorem su7AlphaStrongFourSourcePrimitiveGenerator_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          su7AlphaStrongFourSourcePrimitiveGenerator s) =
      -((89000 : ℚ) / 128511) := by
  rw [su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent]
  exact alphaStrongBottomedFourSource_inverseResidual

/-! ## Canonical output -/

/-- THEOREM 1: the canonical SU(7) data generator is exactly the independent
four-source contribution function. -/
theorem su7AlphaStrongFourSourceGenerator_canonical_eq_independent :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data =
      alphaStrongFourSourceIndependentContribution := by
  funext s
  cases s <;> rfl

/-- THEOREM 1b: the canonical data generator is the bundled encoding of the
source-level primitive generator. -/
theorem su7AlphaStrongFourSourceGenerator_canonical_eq_primitive :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data =
      su7AlphaStrongFourSourcePrimitiveGenerator := by
  rw [su7AlphaStrongFourSourceGenerator_canonical_eq_independent,
    su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent]

/-- THEOREM 2: the generator output has the requested four-source normal form:
`{89/10000, 0, 0, 0}`. -/
theorem su7AlphaStrongFourSourceGenerator_canonical_normalForm :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data .su7Breaking =
        (89 : ℚ) / 10000 ∧
      su7AlphaStrongFourSourceGenerator canonicalSU7Data .threshold = 0 ∧
        su7AlphaStrongFourSourceGenerator canonicalSU7Data .threeLoopRG = 0 ∧
          su7AlphaStrongFourSourceGenerator canonicalSU7Data
              .higgsExtraRepresentation = 0 := by
  rw [su7AlphaStrongFourSourceGenerator_canonical_eq_independent]
  exact alphaStrongFourSourceIndependentContribution_bottomedNormalForm

/-- THEOREM 3: the generated four-source vector sums to the displayed
alpha-level gap. -/
theorem su7AlphaStrongFourSourceGenerator_canonical_sum_eq_gap :
    (∑ s : AlphaStrongResidualSource,
        su7AlphaStrongFourSourceGenerator canonicalSU7Data s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [su7AlphaStrongFourSourceGenerator_canonical_eq_independent]
  exact alphaStrongFourSourceIndependentContribution_bottomedSum_eq_gap

/-- THEOREM 4: the generated four-source vector transports to the exact
inverse residual `-89000/128511`. -/
theorem su7AlphaStrongFourSourceGenerator_canonical_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          su7AlphaStrongFourSourceGenerator canonicalSU7Data s) =
      -((89000 : ℚ) / 128511) := by
  rw [su7AlphaStrongFourSourceGenerator_canonical_eq_independent]
  exact alphaStrongBottomedFourSource_inverseResidual

/-! ## Bundled generator certificate -/

/-- Generator-centered certificate for the alpha_s producer.

This is intentionally downstream of the generator: the core object is
`su7AlphaStrongFourSourceGenerator`, and the certificate only records its
canonical output and residual transport. -/
structure SU7AlphaStrongFourSourceGeneratorCertificate : Prop where
  source_generator_eq_independent_contribution :
    su7AlphaStrongFourSourcePrimitiveGenerator =
      alphaStrongFourSourceIndependentContribution
  canonical_generator_eq_source_generator :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data =
      su7AlphaStrongFourSourcePrimitiveGenerator
  source_generated_normal_form :
    su7AlphaStrongFourSourcePrimitiveGenerator .su7Breaking =
        (89 : ℚ) / 10000 ∧
      su7AlphaStrongFourSourcePrimitiveGenerator .threshold = 0 ∧
        su7AlphaStrongFourSourcePrimitiveGenerator .threeLoopRG = 0 ∧
          su7AlphaStrongFourSourcePrimitiveGenerator
              .higgsExtraRepresentation = 0
  source_generated_sum :
    (∑ s : AlphaStrongResidualSource,
        su7AlphaStrongFourSourcePrimitiveGenerator s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ
  source_generated_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          su7AlphaStrongFourSourcePrimitiveGenerator s) =
      -((89000 : ℚ) / 128511)
  generator_eq_independent_contribution :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data =
      alphaStrongFourSourceIndependentContribution
  generated_normal_form :
    su7AlphaStrongFourSourceGenerator canonicalSU7Data .su7Breaking =
        (89 : ℚ) / 10000 ∧
      su7AlphaStrongFourSourceGenerator canonicalSU7Data .threshold = 0 ∧
        su7AlphaStrongFourSourceGenerator canonicalSU7Data .threeLoopRG = 0 ∧
          su7AlphaStrongFourSourceGenerator canonicalSU7Data
              .higgsExtraRepresentation = 0
  generated_sum :
    (∑ s : AlphaStrongResidualSource,
        su7AlphaStrongFourSourceGenerator canonicalSU7Data s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ
  generated_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          su7AlphaStrongFourSourceGenerator canonicalSU7Data s) =
      -((89000 : ℚ) / 128511)
  card_source :
    AlphaStrongSU7BreakingCardSourceProducerCertificate

/-- THEOREM 5: canonical SU(7) alpha_s four-source generator certificate. -/
theorem su7AlphaStrongFourSourceGeneratorCertificate :
    SU7AlphaStrongFourSourceGeneratorCertificate where
  source_generator_eq_independent_contribution :=
    su7AlphaStrongFourSourcePrimitiveGenerator_eq_independent
  canonical_generator_eq_source_generator :=
    su7AlphaStrongFourSourceGenerator_canonical_eq_primitive
  source_generated_normal_form :=
    su7AlphaStrongFourSourcePrimitiveGenerator_normalForm
  source_generated_sum :=
    su7AlphaStrongFourSourcePrimitiveGenerator_sum_eq_gap
  source_generated_inverse_residual :=
    su7AlphaStrongFourSourcePrimitiveGenerator_inverseResidual
  generator_eq_independent_contribution :=
    su7AlphaStrongFourSourceGenerator_canonical_eq_independent
  generated_normal_form :=
    su7AlphaStrongFourSourceGenerator_canonical_normalForm
  generated_sum :=
    su7AlphaStrongFourSourceGenerator_canonical_sum_eq_gap
  generated_inverse_residual :=
    su7AlphaStrongFourSourceGenerator_canonical_inverseResidual
  card_source :=
    alphaStrongSU7BreakingCardSourceProducerCertificate

end StandardModelConstraint
end SaturationMonoid
