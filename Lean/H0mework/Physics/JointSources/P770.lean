import H0mework.Physics.JointSources.P707
import H0mework.Physics.CouplingSources.P769

/-!
# Proposition 770: input surface welds to the physicalized SU(7) spine

P769 closes the finite numerical chain at the accepted input surface.  This
file removes the remaining presentation split between that input surface and
the already-physicalized SU(7) producer spine:

* the input axis is the QCD inverse-flow slope plus the 4D Poincare slots;
* the input alpha residual is the physicalized finite-geometry residual;
* the input Yukawa depths are the selected SU(7) depth table;
* the input CKM/Jarlskog depth is the physicalized matrix depth;
* the input CKM raw phase is the physicalized matrix raw phase.

So the accepted input surface is not a separate numerical ledger.  It is the
same finite readout seen from the SU(7) representation/RG/CKM spine.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-- THEOREM 1: accepted input surfaces put their axis on the QCD
inverse-coordinate slope plus the 4D Poincare pairing slots. -/
theorem inputSurface_axis_eq_qcdB0_plus_poincareSlots
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    incidenceBetaInputOneAxis C.1.betaInput =
      betaCoeff qcdBlockIncidenceOneLoopInput +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ) := by
  calc
    incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) := by
      exact inputSurfaceFiniteNumerical_axis_eq_ten C hC
    _ =
        betaCoeff qcdBlockIncidenceOneLoopInput +
          (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
            ℚ) := by
      rw [qcd_b0_from_final_carrier_formula,
        AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three]
      norm_num

/-- THEOREM 2: the finite output read from an accepted input surface lies on
the coordinate-spine axis from P707. -/
theorem inputSurface_finiteOutput_axis_eq_coordinateSpine
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (finiteOutputOfFullBetaVectorInput C).axis =
      GrandUnification.traceWeightedQCDPoincareCoordinateAxis := by
  calc
    (finiteOutputOfFullBetaVectorInput C).axis =
        canonicalSourceLawFinitePhysicalOutput.axis := by
      rw [finiteOutputOfFullBetaVectorInput_eq_canonical C hC]
    _ = GrandUnification.traceWeightedQCDPoincareCoordinateAxis :=
      GrandUnification.canonicalFiniteOutput_axis_eq_traceWeightedCoordinateAxis

/-- THEOREM 3: the input alpha residual is the same physicalized finite
geometry residual used by the pressure closure. -/
theorem inputSurface_alphaResidual_eq_physicalizedPressureResidual
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap := by
  calc
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
        -((89000 : ℚ) / 128511) := by
      exact inputSurfaceFiniteNumerical_alphaInverseResidual_eq C hC
    _ =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap := by
      exact
        (GrandUnification.physicalizedNumericalPressureClosureCertificate
          (E := ℂ)).alpha_s_inverse_residual.symm

/-- THEOREM 4: the input Yukawa depth table is the selected SU(7) table from
the physicalized spine. -/
theorem inputSurface_yukawaDepths_eq_physicalizedSelected
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2.massOrder = selectedYukawaDepthTableCandidate.massOrder := by
  calc
    C.2.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
      exact inputSurfaceFiniteNumerical_yukawaMassOrder_eq C hC
    _ = selectedYukawaDepthTableCandidate.massOrder := by
      exact
        su7PhysicalizedNumericalProducerSpineCertificate.nine_yukawa_depths.symm

/-- THEOREM 5: the input CKM/Jarlskog depth is the physicalized matrix depth. -/
theorem inputSurface_ckmDepth_eq_physicalizedMatrixDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
      (ckmJarlskogDepthFromMatrix : ℚ) :=
  inputSurfaceCKMDepth_eq_matrixDepth C hC

/-- THEOREM 6: the input CKM raw phase is the physicalized matrix raw phase. -/
theorem inputSurface_ckmRawPhase_eq_physicalizedMatrixPhase
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogDepthFromMatrix : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
  calc
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
        cpRawPhaseClaim ℚ := by
      exact inputSurfaceFiniteNumerical_rawPhase_eq C hC
    _ =
      (ckmJarlskogDepthFromMatrix : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
      exact ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim.symm

/-- The accepted input surface and the physicalized SU(7) spine are the same
finite producer readout. -/
structure InputSurfacePhysicalizedProducerBridgeCertificate : Prop where
  input_surface_closure :
    Nonempty InputSurfaceFiniteNumericalClosureCertificate
  physicalized_spine :
    SU7PhysicalizedNumericalProducerSpineCertificate
  physicalized_pressure :
    GrandUnification.PhysicalizedNumericalPressureClosureCertificate ℂ
  physicalized_ckm_phase :
    PhysicalizedCKMPhaseProducerCertificate
  axis_eq_qcd_b0_plus_poincare_slots :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        incidenceBetaInputOneAxis C.1.betaInput =
          betaCoeff qcdBlockIncidenceOneLoopInput +
            (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
              ℚ)
  finite_output_axis_eq_coordinate_spine :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (finiteOutputOfFullBetaVectorInput C).axis =
          GrandUnification.traceWeightedQCDPoincareCoordinateAxis
  alpha_residual_matches_physicalized :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPhysicalFiniteGeometryProducer
              currentFormalFourDPoincareCertificate
              unifiedGaugeIntoAlphaEMStructural).producedGap
  yukawa_depths_match_physicalized :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = selectedYukawaDepthTableCandidate.massOrder
  ckm_depth_matches_physicalized :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
          (ckmJarlskogDepthFromMatrix : ℚ)
  ckm_raw_phase_matches_physicalized :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          (ckmJarlskogDepthFromMatrix : ℚ) *
            sigmaGUTTwoLoopExact ℚ

/-- THEOREM 7: the P769 accepted input surface is welded to the P763/P764/P765
physicalized SU(7) numerical spine. -/
theorem inputSurfacePhysicalizedProducerBridgeCertificate :
    InputSurfacePhysicalizedProducerBridgeCertificate where
  input_surface_closure :=
    ⟨inputSurfaceFiniteNumericalClosureCertificate⟩
  physicalized_spine :=
    su7PhysicalizedNumericalProducerSpineCertificate
  physicalized_pressure :=
    GrandUnification.physicalizedNumericalPressureClosureCertificate (E := ℂ)
  physicalized_ckm_phase :=
    physicalizedCKMPhaseProducerCertificate
  axis_eq_qcd_b0_plus_poincare_slots :=
    inputSurface_axis_eq_qcdB0_plus_poincareSlots
  finite_output_axis_eq_coordinate_spine :=
    inputSurface_finiteOutput_axis_eq_coordinateSpine
  alpha_residual_matches_physicalized :=
    inputSurface_alphaResidual_eq_physicalizedPressureResidual
  yukawa_depths_match_physicalized :=
    inputSurface_yukawaDepths_eq_physicalizedSelected
  ckm_depth_matches_physicalized :=
    inputSurface_ckmDepth_eq_physicalizedMatrixDepth
  ckm_raw_phase_matches_physicalized :=
    inputSurface_ckmRawPhase_eq_physicalizedMatrixPhase

end StandardModelConstraint
end SaturationMonoid
