import H0mework.Physics.CouplingSources.P763
import H0mework.Physics.SourceForms.P777

/-!
# Proposition 778: SU(7) representation/matter/Higgs producer source normal form

P762 proves the concrete SU(7) representation/trace layer:

* the block-diagonal `SU(3) x SU(2) x U(1)` embedding into `SU(7)` is
  injective;
* the `3+2+1+1` block-incidence carrier reconstructs the matter/Higgs trace;
* the finite multiplet carrier is anomaly-free;
* the oriented anomaly equations select the Standard-Model hypercharge branch;
* the QCD incidence input gives `b0 = 7`.

P763 connects that representation layer to the finite numerical spine, and
P777 connects the numerical spine to the three source-normal-form producer
nails.  This file packages the whole representation -> matter/Higgs trace ->
RG/Yukawa/CKM source-normal-form chain as one citeable certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Focused representation/matter/Higgs normal-form projections -/

/-- THEOREM 1: the SU(7) incidence carrier has the forced six-slot
matter/Higgs shape. -/
theorem su7RepresentationMatterHiggsNormalForm_incidenceShape :
    Fintype.card SU7BlockIncidence = 6 ∧
      Fintype.card SU7GeneratedCarrierSlot = 6 ∧
        Nonempty (SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) ∧
          (∀ G : StandardModelGaugeFactor,
            incidenceCarrierTraceInput G = multipletCarrierTraceInput G) := by
  exact
    ⟨SU7BlockIncidence.card,
      SU7GeneratedCarrierSlot.card,
      ⟨blockIncidenceGeneratedSlotEquiv⟩,
      incidenceCarrierTraceInput_eq_multipletCarrierTraceInput⟩

/-- THEOREM 2: the block-incidence carrier computes all three
Standard-Model one-loop residual/asymptotic slopes. -/
theorem su7RepresentationMatterHiggsNormalForm_b0Values :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff (incidenceCarrierTraceInput .weakSU2) = (19 : ℚ) / 6 ∧
        betaCoeff (incidenceCarrierTraceInput .hyperchargeU1) =
          -((41 : ℚ) / 6) ∧
          (∀ G : StandardModelGaugeFactor,
            betaCoeff (incidenceCarrierTraceInput G) =
              standardModelAsymptoticB0 G) := by
  exact
    ⟨qcd_b0_from_block_incidence_carrier,
      weak_b0_from_block_incidence_carrier,
      hypercharge_b0_from_block_incidence_carrier,
      standardModel_b0_from_block_incidence_carrier⟩

/-- THEOREM 3: the unified one-loop carrier fixes the residual self-bump
dynamics for all three gauge factors. -/
theorem su7RepresentationMatterHiggsNormalForm_runningDelta :
    (∀ G : StandardModelGaugeFactor, ∀ σ : ℝ,
      (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
        -((betaCoeff (incidenceCarrierTraceInput G) : ℚ) : ℝ) * σ ^ 2) ∧
      (∀ σ : ℝ,
        (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
          -(7 : ℝ) * σ ^ 2) ∧
        (∀ σ : ℝ,
          (standardModelOneLoopCarrier .weakSU2).residualSelfBumpStep σ - σ =
            -((19 : ℝ) / 6) * σ ^ 2) ∧
          (∀ σ : ℝ,
            (standardModelOneLoopCarrier .hyperchargeU1).residualSelfBumpStep σ - σ =
              ((41 : ℝ) / 6) * σ ^ 2) := by
  exact
    ⟨standardModelResidualSelfBump_delta_incidenceCarrierFormula,
      color_residualSelfBump_delta_from_unified_carrier,
      weak_residualSelfBump_delta_from_unified_carrier,
      hypercharge_residualSelfBump_delta_from_unified_carrier⟩

/-- THEOREM 4: the representation layer and the numerical three-nail spine
share the same QCD/Yukawa/CKM readout. -/
theorem su7RepresentationMatterHiggsNormalForm_numericalSpine :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) := by
  exact
    su7PhysicalizedNumericalProducerSpineCertificate.qcd_and_ckm_spine_summary

/-! ## Bundled certificate -/

/-- Source-normal-form certificate for the representation ->
matter/Higgs/RG/Yukawa/CKM producer chain. -/
structure SU7RepresentationMatterHiggsSourceNormalFormCertificate : Prop where
  representation_rg :
    SU7RepresentationPhysicalizedRGFlowProducerCertificate
  physicalized_numerical_spine :
    SU7PhysicalizedNumericalProducerSpineCertificate
  three_nail_source_normal_form :
    StandardModelThreeNailProducerSourceNormalFormCertificate
  one_loop_carrier :
    Nonempty StandardModelOneLoopCarrierFinalReceipt
  incidence_matter_carrier :
    Nonempty SU7BlockIncidenceMatterCarrierCertificate
  representation_physicalization :
    Nonempty SU7RepresentationPhysicalizationReceipt
  block_embedding_injective :
    Function.Injective GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7
  anomaly_cancellation :
    Nonempty StandardModelMultipletAnomalyCancellationCertificate
  oriented_hypercharge_unique :
    ∀ Y : OneGenerationHyperchargeAssignment,
      Y.colorAnomalyFree ->
      Y.weakAnomalyFree ->
      Y.gravitationalAnomalyFree ->
      Y.cubicAnomalyFree ->
      Y.e = 1 ->
      Y.u < Y.d ->
      Y = OneGenerationHyperchargeAssignment.standardModel
  block_dimension_sum :
    SU7CarrierBlock.fundamentalDimension .color +
      SU7CarrierBlock.fundamentalDimension .weak +
      SU7CarrierBlock.fundamentalDimension .positiveSinglet +
      SU7CarrierBlock.fundamentalDimension .negativeSinglet = 7
  incidence_shape :
    Fintype.card SU7BlockIncidence = 6 ∧
      Fintype.card SU7GeneratedCarrierSlot = 6 ∧
        Nonempty (SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) ∧
          (∀ G : StandardModelGaugeFactor,
            incidenceCarrierTraceInput G = multipletCarrierTraceInput G)
  b0_values :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff (incidenceCarrierTraceInput .weakSU2) = (19 : ℚ) / 6 ∧
        betaCoeff (incidenceCarrierTraceInput .hyperchargeU1) =
          -((41 : ℚ) / 6) ∧
          (∀ G : StandardModelGaugeFactor,
            betaCoeff (incidenceCarrierTraceInput G) =
              standardModelAsymptoticB0 G)
  running_delta :
    (∀ G : StandardModelGaugeFactor, ∀ σ : ℝ,
      (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
        -((betaCoeff (incidenceCarrierTraceInput G) : ℚ) : ℝ) * σ ^ 2) ∧
      (∀ σ : ℝ,
        (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
          -(7 : ℝ) * σ ^ 2) ∧
        (∀ σ : ℝ,
          (standardModelOneLoopCarrier .weakSU2).residualSelfBumpStep σ - σ =
            -((19 : ℝ) / 6) * σ ^ 2) ∧
          (∀ σ : ℝ,
            (standardModelOneLoopCarrier .hyperchargeU1).residualSelfBumpStep σ - σ =
              ((41 : ℝ) / 6) * σ ^ 2)
  qcd_inverse_flow_slope :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .colorSU3 sigma0 t =
        (1 : ℝ) / sigma0 +
          ((betaCoeff qcdBlockIncidenceOneLoopInput : ℚ) : ℝ) * t
  numerical_spine :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)
  alpha_closure :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) ∧
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
        alphaStrongDisplayed ℚ

/-- THEOREM 5: SU(7) representation/matter/Higgs producer source normal
form. -/
theorem su7RepresentationMatterHiggsSourceNormalFormCertificate :
    SU7RepresentationMatterHiggsSourceNormalFormCertificate where
  representation_rg :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate
  physicalized_numerical_spine :=
    su7PhysicalizedNumericalProducerSpineCertificate
  three_nail_source_normal_form :=
    standardModelThreeNailProducerSourceNormalFormCertificate
  one_loop_carrier :=
    ⟨standardModelOneLoopCarrierFinalReceipt⟩
  incidence_matter_carrier :=
    ⟨su7BlockIncidenceMatterCarrierCertificate⟩
  representation_physicalization :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.representation_physicalization
  block_embedding_injective :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.block_embedding_injective
  anomaly_cancellation :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.anomaly_cancellation
  oriented_hypercharge_unique :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.oriented_hypercharge_unique
  block_dimension_sum :=
    standardModelOneLoopCarrierFinalReceipt.block_dimension_sum
  incidence_shape :=
    su7RepresentationMatterHiggsNormalForm_incidenceShape
  b0_values :=
    su7RepresentationMatterHiggsNormalForm_b0Values
  running_delta :=
    su7RepresentationMatterHiggsNormalForm_runningDelta
  qcd_inverse_flow_slope :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.qcd_inverse_flow_slope_from_representation
  numerical_spine :=
    su7RepresentationMatterHiggsNormalForm_numericalSpine
  alpha_closure :=
    standardModelThreeNailProducerSourceNormalFormCertificate.alpha_closure

end StandardModelConstraint
end SaturationMonoid
