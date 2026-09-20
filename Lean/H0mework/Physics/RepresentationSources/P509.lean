/-
  Proposition 509: concrete typed support reconstructs the one-loop trace
  input.

  P508 proves that the concrete canonical matrix support fibers reproduce the
  component counts of the accepted matter/Higgs carrier.  This file feeds those
  concrete fiber counts back into the trace layer:

      concrete typed support -> Weyl/Higgs trace input -> carrier b0.

  Boundary: the universal one-loop coefficient formula and the representation
  schedule are still inherited from earlier certificates.  The new result here
  is mechanism-faithfulness of the concrete support counts with respect to the
  trace input already used by P456/P459/P503.
-/

import H0mework.Physics.JointSources.P508

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

/-! ## Per-generation traces reconstructed from concrete support fibers -/

/-- QCD Dynkin trace per generation reconstructed from concrete support
fibers.  Colored slots contribute one fundamental trace for each weak/singlet
copy, i.e. `fiber/3` copies of the color fundamental. -/
def concreteSupportColorWeylTracePerGeneration : ℚ :=
  ((Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) : ℚ) / 3) * (1 / 2) +
    ((Fintype.card (ConcreteMatterSlotFiber .upConjugate) : ℚ) / 3) * (1 / 2) +
    ((Fintype.card (ConcreteMatterSlotFiber .downConjugate) : ℚ) / 3) * (1 / 2)

/-- Weak-isospin Dynkin trace per generation reconstructed from concrete
support fibers.  Weak-doublet slots contribute one fundamental trace for each
color/singlet copy, i.e. `fiber/2` weak doublets. -/
def concreteSupportWeakWeylTracePerGeneration : ℚ :=
  ((Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) : ℚ) / 2) * (1 / 2) +
    ((Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) : ℚ) / 2) * (1 / 2)

/-- Hypercharge-square Weyl trace per generation reconstructed from concrete
support fibers and P457's signed hypercharges. -/
def concreteSupportHyperchargeSquareTracePerGeneration : ℚ :=
  (Fintype.card (ConcreteMatterSlotFiber .quarkDoublet) : ℚ) *
      StandardModelWeylMultiplet.hypercharge .quarkDoublet ^ 2 +
    (Fintype.card (ConcreteMatterSlotFiber .upConjugate) : ℚ) *
      StandardModelWeylMultiplet.hypercharge .upConjugate ^ 2 +
    (Fintype.card (ConcreteMatterSlotFiber .downConjugate) : ℚ) *
      StandardModelWeylMultiplet.hypercharge .downConjugate ^ 2 +
    (Fintype.card (ConcreteMatterSlotFiber .leptonDoublet) : ℚ) *
      StandardModelWeylMultiplet.hypercharge .leptonDoublet ^ 2 +
    (Fintype.card (ConcreteMatterSlotFiber .electronConjugate) : ℚ) *
      StandardModelWeylMultiplet.hypercharge .electronConjugate ^ 2

/-- THEOREM 1: the concrete-support QCD trace is the P456 generation trace. -/
theorem concreteSupportColorWeylTracePerGeneration_eq_generationTrace :
    concreteSupportColorWeylTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.colorDynkinTrace := by
  norm_num [concreteSupportColorWeylTracePerGeneration,
    concreteMatterSlotFiber_card_eq_componentMultiplicity,
    matterSlotComponentMultiplicity,
    StandardModelWeylMultiplet.generationTrace,
    StandardModelWeylMultiplet.colorDynkinTrace]

/-- THEOREM 2: the concrete-support weak trace is the P456 generation trace. -/
theorem concreteSupportWeakWeylTracePerGeneration_eq_generationTrace :
    concreteSupportWeakWeylTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.weakDynkinTrace := by
  norm_num [concreteSupportWeakWeylTracePerGeneration,
    concreteMatterSlotFiber_card_eq_componentMultiplicity,
    matterSlotComponentMultiplicity,
    StandardModelWeylMultiplet.generationTrace,
    StandardModelWeylMultiplet.weakDynkinTrace]

/-- THEOREM 3: the concrete-support hypercharge-square trace is the P456
generation trace. -/
theorem concreteSupportHyperchargeSquareTracePerGeneration_eq_generationTrace :
    concreteSupportHyperchargeSquareTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.hyperchargeSquareTrace := by
  norm_num [concreteSupportHyperchargeSquareTracePerGeneration,
    concreteMatterSlotFiber_card_eq_componentMultiplicity,
    matterSlotComponentMultiplicity,
    StandardModelWeylMultiplet.generationTrace,
    StandardModelWeylMultiplet.hyperchargeSquareTrace,
    StandardModelWeylMultiplet.hypercharge]

/-! ## Three-generation and Higgs traces from concrete support -/

/-- Total Weyl trace after applying the three Poincare generation slots. -/
def concreteSupportTotalWeylTrace (perGeneration : ℚ) : ℚ :=
  (Fintype.card StandardModelFermionGeneration : ℚ) * perGeneration

/-- THEOREM 4: concrete-support total QCD Weyl trace is `6`. -/
theorem concreteSupportTotalColorWeylTrace :
    concreteSupportTotalWeylTrace
      concreteSupportColorWeylTracePerGeneration = 6 := by
  rw [concreteSupportTotalWeylTrace,
    concreteSupportColorWeylTracePerGeneration_eq_generationTrace,
    StandardModelWeylMultiplet.colorDynkinTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- THEOREM 5: concrete-support total weak Weyl trace is `6`. -/
theorem concreteSupportTotalWeakWeylTrace :
    concreteSupportTotalWeylTrace
      concreteSupportWeakWeylTracePerGeneration = 6 := by
  rw [concreteSupportTotalWeylTrace,
    concreteSupportWeakWeylTracePerGeneration_eq_generationTrace,
    StandardModelWeylMultiplet.weakDynkinTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- THEOREM 6: concrete-support total hypercharge Weyl trace is `10`. -/
theorem concreteSupportTotalHyperchargeWeylTrace :
    concreteSupportTotalWeylTrace
      concreteSupportHyperchargeSquareTracePerGeneration = 10 := by
  rw [concreteSupportTotalWeylTrace,
    concreteSupportHyperchargeSquareTracePerGeneration_eq_generationTrace,
    StandardModelWeylMultiplet.hyperchargeSquareTrace_sum,
    standardModel_generation_count_three]
  norm_num

/-- Higgs scalar trace reconstructed from the concrete two-component Higgs
fiber. -/
def concreteSupportHiggsScalarTrace : StandardModelGaugeFactor -> ℚ
  | .colorSU3 => 0
  | .weakSU2 =>
      ((Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) : ℚ) / 2) *
        (1 / 2)
  | .hyperchargeU1 =>
      (Fintype.card (ConcreteMatterSlotFiber .higgsDoublet) : ℚ) *
        (1 / 2) ^ 2

/-- THEOREM 7: concrete Higgs support reconstructs P456's scalar trace. -/
theorem concreteSupportHiggsScalarTrace_eq_higgsScalarTrace
    (G : StandardModelGaugeFactor) :
    concreteSupportHiggsScalarTrace G = higgsScalarTrace G := by
  cases G <;>
    norm_num [concreteSupportHiggsScalarTrace, higgsScalarTrace,
      concreteMatterSlotFiber_card_higgsDoublet]

/-! ## Concrete support trace input and carrier b0 -/

/-- Gauge trace input reconstructed from concrete typed matrix support. -/
def concreteSupportCarrierTraceInput :
    StandardModelGaugeFactor -> GaugeTraceOneLoopInput
  | .colorSU3 =>
      { adjointCasimir := 3
        weylDynkinTrace :=
          concreteSupportTotalWeylTrace
            concreteSupportColorWeylTracePerGeneration
        scalarDynkinTrace := concreteSupportHiggsScalarTrace .colorSU3 }
  | .weakSU2 =>
      { adjointCasimir := 2
        weylDynkinTrace :=
          concreteSupportTotalWeylTrace
            concreteSupportWeakWeylTracePerGeneration
        scalarDynkinTrace := concreteSupportHiggsScalarTrace .weakSU2 }
  | .hyperchargeU1 =>
      { adjointCasimir := 0
        weylDynkinTrace :=
          concreteSupportTotalWeylTrace
            concreteSupportHyperchargeSquareTracePerGeneration
        scalarDynkinTrace :=
          concreteSupportHiggsScalarTrace .hyperchargeU1 }

/-- THEOREM 8: concrete support reconstructs the finite multiplet trace input. -/
theorem concreteSupportCarrierTraceInput_eq_multipletCarrierTraceInput
    (G : StandardModelGaugeFactor) :
    concreteSupportCarrierTraceInput G = multipletCarrierTraceInput G := by
  cases G
  · rw [concreteSupportCarrierTraceInput, multipletCarrierTraceInput,
      concreteSupportTotalColorWeylTrace,
      total_colorWeylTrace,
      concreteSupportHiggsScalarTrace_eq_higgsScalarTrace]
  · rw [concreteSupportCarrierTraceInput, multipletCarrierTraceInput,
      concreteSupportTotalWeakWeylTrace,
      total_weakWeylTrace,
      concreteSupportHiggsScalarTrace_eq_higgsScalarTrace]
  · rw [concreteSupportCarrierTraceInput, multipletCarrierTraceInput,
      concreteSupportTotalHyperchargeWeylTrace,
      total_hyperchargeWeylTrace,
      concreteSupportHiggsScalarTrace_eq_higgsScalarTrace]

/-- THEOREM 9: the concrete typed support forces the same carrier `b0`. -/
theorem betaCoeff_concreteSupportCarrierTraceInput_eq_carrierB0
    (G : StandardModelGaugeFactor) :
    betaCoeff (concreteSupportCarrierTraceInput G) = carrierB0 G := by
  rw [concreteSupportCarrierTraceInput_eq_multipletCarrierTraceInput,
    betaCoeff_multipletCarrierTraceInput_eq_carrierB0]

/-- Bundled receipt: concrete typed matrix support reconstructs the trace
input and hence the same one-loop carrier coefficient. -/
structure ConcreteSupportTraceInputCertificate : Prop where
  color_generation_trace :
    concreteSupportColorWeylTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.colorDynkinTrace
  weak_generation_trace :
    concreteSupportWeakWeylTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.weakDynkinTrace
  hypercharge_generation_trace :
    concreteSupportHyperchargeSquareTracePerGeneration =
      StandardModelWeylMultiplet.generationTrace
        StandardModelWeylMultiplet.hyperchargeSquareTrace
  higgs_scalar_trace :
    ∀ G : StandardModelGaugeFactor,
      concreteSupportHiggsScalarTrace G = higgsScalarTrace G
  trace_input :
    ∀ G : StandardModelGaugeFactor,
      concreteSupportCarrierTraceInput G = multipletCarrierTraceInput G
  b0_projection :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (concreteSupportCarrierTraceInput G) = carrierB0 G
  representation_typing :
    ConcreteMatterRepresentationTypingCertificate

/-- THEOREM 10: concrete support is trace-faithful to the existing
Standard-Model matter/Higgs carrier. -/
theorem concreteSupportTraceInputCertificate :
    ConcreteSupportTraceInputCertificate where
  color_generation_trace :=
    concreteSupportColorWeylTracePerGeneration_eq_generationTrace
  weak_generation_trace :=
    concreteSupportWeakWeylTracePerGeneration_eq_generationTrace
  hypercharge_generation_trace :=
    concreteSupportHyperchargeSquareTracePerGeneration_eq_generationTrace
  higgs_scalar_trace := concreteSupportHiggsScalarTrace_eq_higgsScalarTrace
  trace_input := concreteSupportCarrierTraceInput_eq_multipletCarrierTraceInput
  b0_projection := betaCoeff_concreteSupportCarrierTraceInput_eq_carrierB0
  representation_typing := concreteMatterRepresentationTypingCertificate

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
