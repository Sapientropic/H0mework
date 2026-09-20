import H0mework.Physics.AlphaSources.P641

/-!
# Proposition 642: block-incidence receipt for the alpha_s source-label producer

P641 proves the current positive selector: finite-geometry surface membership
recovers the `SU(7)` active source label and is not a scalar-gap-only rule.
This file hooks that selector back to the upstream finite Standard-Model
carrier:

* P460/P461 endpoint-signature uniqueness fixes the incidence schedule;
* P461 gives `b0(QCD)=7` from the `3+2+1+1` block-incidence carrier;
* P523/P618 package this representation/QCD/Poincare layer as the physical
  finite-geometry alpha_s producer;
* P641 then recovers the active source label `su7Breaking`, and P618 transports
  the gap to the exact inverse residual `-89000/128511`.

Boundary: this is still the finite block-incidence producer certificate.  It
does not compute a smooth threshold spectrum, three-loop RG correction, or
Higgs-extra-representation threshold.  It closes the current finite producer
chain from block incidence to source label and exact residual.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Upstream block-incidence/QCD facts exposed at the alpha_s producer layer -/

/-- THEOREM 1: endpoint signatures uniquely fix the current SU(7)
incidence-to-generated-slot schedule. -/
theorem alphaStrongBlockIncidence_endpointSchedule_unique :
    ∀ f :
        RunningSigmaBeta.SU7BlockIncidence ->
          RunningSigmaBeta.SU7GeneratedCarrierSlot,
      (∀ i : RunningSigmaBeta.SU7BlockIncidence,
        RunningSigmaBeta.generatedSlotEndpointSignature (f i) =
          RunningSigmaBeta.SU7BlockIncidence.endpoints i) ->
        f = RunningSigmaBeta.generatedSlotOfIncidence := by
  intro f hf
  exact RunningSigmaBeta.qcdCarrierB0FinalReceipt.schedule_unique f hf

/-- THEOREM 2: the upstream block-incidence carrier gives the QCD one-loop
coefficient `b0 = 7`. -/
theorem alphaStrongBlockIncidence_qcdB0_eq_seven :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7 := by
  exact RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula

/-- THEOREM 3: the SU(7) representation-physicalization receipt exposes the
same block-incidence QCD coefficient. -/
theorem alphaStrongRepresentationPhysicalization_qcdB0_eq_seven :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7 := by
  exact su7RepresentationPhysicalizationReceipt.qcd_b0

/-! ## The finite physical producer selects SU7 and produces the exact residual -/

/-- THEOREM 4: the block-incidence physical producer is selected as
`su7Breaking` by the P641 source-label selector. -/
theorem alphaStrongBlockIncidencePhysicalProducer_selects_su7
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    alphaStrongFiniteGeometryActiveSourceSelector
        ((alphaStrongPhysicalFiniteGeometryProducer C e)
          |>.toFourSourceClosureReceipt) =
      AlphaStrongResidualSource.su7Breaking := by
  exact alphaStrongPhysicalFiniteGeometryProducer_receiptSelector_su7 C e

/-- THEOREM 5: the block-incidence physical producer carries singleton active
support at `su7Breaking`. -/
theorem alphaStrongBlockIncidencePhysicalProducer_activeSupport_iff
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport
        (alphaStrongPhysicalFiniteGeometryProducer C e).contribution s ↔
      s = .su7Breaking := by
  exact alphaStrongPhysicalFiniteGeometryProducer_activeSupport_iff C e s

/-- THEOREM 6: the block-incidence physical producer gives the exact inverse
alpha_s residual needed to close the displayed coupling. -/
theorem alphaStrongBlockIncidencePhysicalProducer_inverseResidual
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer C e).producedGap =
      -((89000 : ℚ) / 128511) := by
  exact alphaStrongPhysicalFiniteGeometryProducer_inverseCorrection C e

/-- THEOREM 7: the same producer closes the displayed alpha_s value after
inverse-coordinate transport. -/
theorem alphaStrongBlockIncidencePhysicalProducer_closes_displayedAlpha
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPhysicalFiniteGeometryProducer C e).producedGap) =
      alphaStrongDisplayed ℚ := by
  exact alphaStrongPhysicalFiniteGeometryProducer_closes_displayedAlpha C e

/-! ## Receipt -/

/-- Compact receipt for the current upstream-to-output finite alpha_s
producer chain.

The fields deliberately keep the scalar no-go visible: a source-sensitive
finite-geometry selector is necessary, and the block-incidence/QCD/Poincare
receipt supplies the positive selector and the exact residual. -/
structure AlphaStrongBlockIncidenceSourceLabelProducerCertificate where
  orientation :
    RunningSigmaBeta.SU7IncidenceOrientationUniquenessCertificate
  qcd_final :
    RunningSigmaBeta.QCDCarrierB0FinalReceipt
  representation :
    SU7RepresentationPhysicalizationReceipt
  finite_source_label :
    AlphaStrongFiniteGeometrySourceLabelProducerCertificate
  endpoint_schedule_unique :
    ∀ f :
        RunningSigmaBeta.SU7BlockIncidence ->
          RunningSigmaBeta.SU7GeneratedCarrierSlot,
      (∀ i : RunningSigmaBeta.SU7BlockIncidence,
        RunningSigmaBeta.generatedSlotEndpointSignature (f i) =
          RunningSigmaBeta.SU7BlockIncidence.endpoints i) ->
        f = RunningSigmaBeta.generatedSlotOfIncidence
  qcd_b0_from_block_incidence :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  physical_producer_selects_su7 :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        alphaStrongFiniteGeometryActiveSourceSelector
            ((alphaStrongPhysicalFiniteGeometryProducer C e)
              |>.toFourSourceClosureReceipt) =
          AlphaStrongResidualSource.su7Breaking
  physical_producer_active_support :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier)
      (s : AlphaStrongResidualSource),
        AlphaStrongResidualActiveSourceSupport
            (alphaStrongPhysicalFiniteGeometryProducer C e).contribution s ↔
          s = .su7Breaking
  physical_inverse_residual :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPhysicalFiniteGeometryProducer C e).producedGap =
          -((89000 : ℚ) / 128511)
  physical_closes_displayed_alpha :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                (alphaStrongPhysicalFiniteGeometryProducer C e).producedGap) =
          alphaStrongDisplayed ℚ
  selector_not_total_gap_only :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteGeometryActiveSourceSelector

/-- THEOREM 8: block-incidence source-label producer certificate. -/
def alphaStrongBlockIncidenceSourceLabelProducerCertificate :
    AlphaStrongBlockIncidenceSourceLabelProducerCertificate where
  orientation := RunningSigmaBeta.su7IncidenceOrientationUniquenessCertificate
  qcd_final := RunningSigmaBeta.qcdCarrierB0FinalReceipt
  representation := su7RepresentationPhysicalizationReceipt
  finite_source_label := alphaStrongFiniteGeometrySourceLabelProducerCertificate
  endpoint_schedule_unique := alphaStrongBlockIncidence_endpointSchedule_unique
  qcd_b0_from_block_incidence := alphaStrongBlockIncidence_qcdB0_eq_seven
  physical_producer_selects_su7 := by
    intro C e
    exact alphaStrongBlockIncidencePhysicalProducer_selects_su7 C e
  physical_producer_active_support := by
    intro C e s
    exact alphaStrongBlockIncidencePhysicalProducer_activeSupport_iff C e s
  physical_inverse_residual := by
    intro C e
    exact alphaStrongBlockIncidencePhysicalProducer_inverseResidual C e
  physical_closes_displayed_alpha := by
    intro C e
    exact alphaStrongBlockIncidencePhysicalProducer_closes_displayedAlpha C e
  selector_not_total_gap_only :=
    alphaStrongFiniteGeometryActiveSourceSelector_not_totalGapOnly

end StandardModelConstraint
end SaturationMonoid
