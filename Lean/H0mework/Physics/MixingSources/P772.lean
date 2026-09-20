import H0mework.Physics.YukawaSources.P666
import H0mework.Physics.AlphaSources.P771

/-!
# Proposition 772: input-surface Yukawa/CKM source decomposition

P771 decomposes the accepted input-surface alpha residual into the singleton
SU(7)-breaking source.  This file does the matching job for the Yukawa/CKM
leg:

* the input Yukawa table is on the full beta-vector surface;
* hence it is on the SU(7) primitive depth surface;
* hence it is the selected table;
* the selected table is exactly the canonical primitive-card coefficient
  endpoint schedule;
* its CKM/Jarlskog four-product factors, matrix depth, and exact raw phase are
  the same finite object.

So the input Yukawa/CKM leg is not merely numerically equal to the selected
table.  It is the selected primitive-card / endpoint-schedule normal form read
through the accepted input surface.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- THEOREM 1: the Yukawa table of any accepted input surface lies on the
full beta-vector Yukawa-depth producer surface. -/
theorem inputSurface_yukawaTable_fullBetaVectorSurface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    FullBetaVectorYukawaDepthProducerSurface C.2 := by
  exact hC.2

/-- THEOREM 2: the Yukawa table of any accepted input surface lies on the
SU(7) primitive Yukawa-depth producer surface. -/
theorem inputSurface_yukawaTable_su7PrimitiveSurface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    SU7PrimitiveYukawaDepthProducerSurface C.2 := by
  exact
    fullBetaVectorYukawaDepthProducerSurface_to_su7Primitive
      C.2 hC.2

/-- THEOREM 3: any accepted input-surface Yukawa table is the selected
SU(7) depth table. -/
theorem inputSurface_yukawaTable_eq_selected
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2 = selectedYukawaDepthTableCandidate := by
  exact
    eq_selectedYukawaDepthTableCandidate_of_fullBetaVectorProducer
      C.2 hC.2

/-- THEOREM 4: the canonical primitive-card coefficient endpoint schedule is
the selected Yukawa depth table. -/
theorem canonicalCoefficientEndpointSchedule_eq_selectedYukawaTable :
    coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence =
      selectedYukawaDepthTableCandidate := by
  exact
    eq_selectedYukawaDepthTableCandidate_of_su7PrimitiveProducer
      (coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence)
      ⟨canonicalYukawaCoefficientPrimitiveCardPacket,
        yukawaSectorInformationIncidence,
        canonicalYukawaCoefficientPrimitiveCardPacket_sourceEquations,
        yukawaSectorInformationIncidence_endpointPreserving, rfl⟩

/-- THEOREM 5: any accepted input-surface Yukawa table is the canonical
primitive-card coefficient endpoint schedule. -/
theorem inputSurface_yukawaTable_eq_canonicalCoefficientEndpointSchedule
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2 =
      coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence := by
  calc
    C.2 = selectedYukawaDepthTableCandidate := by
      exact inputSurface_yukawaTable_eq_selected C hC
    _ =
      coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence := by
      exact canonicalCoefficientEndpointSchedule_eq_selectedYukawaTable.symm

/-- THEOREM 6: the input-surface mass-order depths are exactly the selected
SU(7) mass-order depths. -/
theorem inputSurface_yukawaMassOrder_eq_selectedMassOrder
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2.massOrder = selectedYukawaDepthTableCandidate.massOrder := by
  exact inputSurface_yukawaDepths_eq_physicalizedSelected C hC

/-- THEOREM 7: the input-surface CKM/Jarlskog four-product depth is the
selected-table four-product depth. -/
theorem inputSurface_ckmFourProduct_eq_selected
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate := by
  rw [inputSurface_yukawaTable_eq_selected C hC]

/-- THEOREM 8: the input-surface table-level CKM depth sum is the
selected-table CKM depth sum. -/
theorem inputSurface_ckmTableSum_eq_selected
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmDepthSum_fromYukawaDepthTable C.2 =
      ckmDepthSum_fromYukawaDepthTable selectedYukawaDepthTableCandidate := by
  rw [inputSurface_yukawaTable_eq_selected C hC]

/-- THEOREM 9: the accepted input-surface table has the four CKM/Jarlskog
factor contributions `(-226, -143, 562, 193)`. -/
theorem inputSurface_ckmFactors_forced
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution C.2 .V_ub_conj = (562 : Int) ∧
          CKMJarlskogFactor.depthContribution C.2 .V_cs_conj = (193 : Int) := by
  rw [inputSurface_yukawaTable_eq_selected C hC]
  exact su7YukawaCKMProducerCertificate.ckm_factors

/-- THEOREM 10: the input-surface CKM/Jarlskog depth is the matrix depth as an
integer identity. -/
theorem inputSurface_ckmDepth_eq_matrixDepth_int
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 = ckmJarlskogDepthFromMatrix := by
  calc
    ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) := by
      exact inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_int C hC
    _ = ckmJarlskogDepthFromMatrix := by
      exact ckmJarlskogDepthFromMatrix_eq_386.symm

/-- THEOREM 11: the input-surface CKM/Jarlskog matrix-object depth agrees with
the input table. -/
theorem inputSurface_ckmDepth_eq_matrixObjectDepth_int
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 =
      ckmJarlskogDepthFromMatrixObject := by
  calc
    ckmJarlskogFourProductDepthSum C.2 = ckmJarlskogDepthFromMatrix := by
      exact inputSurface_ckmDepth_eq_matrixDepth_int C hC
    _ = ckmJarlskogDepthFromMatrixObject := by
      exact ckmJarlskogDepthFromMatrixObject_eq_matrix.symm

/-- THEOREM 12: the input-surface CKM exact raw phase is the matrix exact raw
phase. -/
theorem inputSurface_ckmExactRawPhase_eq_matrix
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogDepthFromMatrix : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
  exact inputSurface_ckmRawPhase_eq_physicalizedMatrixPhase C hC

/-- The accepted input-surface Yukawa/CKM leg is exactly the selected
primitive-card / endpoint-schedule normal form. -/
structure InputSurfaceYukawaCKMSourceDecompositionCertificate : Prop where
  input_surface_physicalized_bridge :
    InputSurfacePhysicalizedProducerBridgeCertificate
  input_surface_alpha_source_decomposition :
    InputSurfaceAlphaSourceDecompositionCertificate
  full_beta_vector_input_surface :
    Nonempty FullBetaVectorInputThreeNailSurfaceCertificate
  yukawa_pressure_root :
    Nonempty (GrandUnification.YukawaLeaveOneOutPressureUnifiedRootCertificate
      ℂ)
  su7_yukawa_ckm :
    Nonempty SU7YukawaCKMProducerCertificate
  physicalized_spine :
    SU7PhysicalizedNumericalProducerSpineCertificate
  primitive_card_source_equations :
    YukawaPrimitiveCardSourceEquations
      canonicalYukawaCoefficientPrimitiveCardPacket
  endpoint_schedule_preserving :
    YukawaSectorEndpointSignaturePreservingSchedule
      yukawaSectorInformationIncidence
  input_table_full_beta_surface :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        FullBetaVectorYukawaDepthProducerSurface C.2
  input_table_su7_primitive_surface :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        SU7PrimitiveYukawaDepthProducerSurface C.2
  input_table_eq_selected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2 = selectedYukawaDepthTableCandidate
  coefficient_endpoint_schedule_eq_selected :
    coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence =
      selectedYukawaDepthTableCandidate
  input_table_eq_coefficient_endpoint_schedule :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2 =
          coefficientScheduleYukawaDepthTableCandidate
            (primitiveCardYukawaDepthStencilCoefficientVector
              canonicalYukawaCoefficientPrimitiveCardPacket)
            yukawaSectorInformationIncidence
  input_mass_order_eq_selected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = selectedYukawaDepthTableCandidate.massOrder
  input_ckm_four_product_eq_selected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 =
          ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate
  input_ckm_table_sum_eq_selected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmDepthSum_fromYukawaDepthTable C.2 =
          ckmDepthSum_fromYukawaDepthTable selectedYukawaDepthTableCandidate
  input_ckm_factors :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
          CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
            CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
              (562 : Int) ∧
              CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
                (193 : Int)
  input_ckm_depth_eq_matrix :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = ckmJarlskogDepthFromMatrix
  input_ckm_depth_eq_matrix_object :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 =
          ckmJarlskogDepthFromMatrixObject
  input_ckm_exact_raw_phase_eq_matrix :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          (ckmJarlskogDepthFromMatrix : ℚ) *
            sigmaGUTTwoLoopExact ℚ

/-- THEOREM 13: input-surface Yukawa/CKM source decomposition certificate. -/
theorem inputSurfaceYukawaCKMSourceDecompositionCertificate :
    InputSurfaceYukawaCKMSourceDecompositionCertificate where
  input_surface_physicalized_bridge :=
    inputSurfacePhysicalizedProducerBridgeCertificate
  input_surface_alpha_source_decomposition :=
    inputSurfaceAlphaSourceDecompositionCertificate
  full_beta_vector_input_surface :=
    ⟨fullBetaVectorInputThreeNailSurfaceCertificate⟩
  yukawa_pressure_root :=
    ⟨GrandUnification.yukawaLeaveOneOutPressureUnifiedRootCertificate
      (E := ℂ)⟩
  su7_yukawa_ckm :=
    ⟨su7YukawaCKMProducerCertificate⟩
  physicalized_spine :=
    su7PhysicalizedNumericalProducerSpineCertificate
  primitive_card_source_equations :=
    canonicalYukawaCoefficientPrimitiveCardPacket_sourceEquations
  endpoint_schedule_preserving :=
    yukawaSectorInformationIncidence_endpointPreserving
  input_table_full_beta_surface :=
    inputSurface_yukawaTable_fullBetaVectorSurface
  input_table_su7_primitive_surface :=
    inputSurface_yukawaTable_su7PrimitiveSurface
  input_table_eq_selected :=
    inputSurface_yukawaTable_eq_selected
  coefficient_endpoint_schedule_eq_selected :=
    canonicalCoefficientEndpointSchedule_eq_selectedYukawaTable
  input_table_eq_coefficient_endpoint_schedule :=
    inputSurface_yukawaTable_eq_canonicalCoefficientEndpointSchedule
  input_mass_order_eq_selected :=
    inputSurface_yukawaMassOrder_eq_selectedMassOrder
  input_ckm_four_product_eq_selected :=
    inputSurface_ckmFourProduct_eq_selected
  input_ckm_table_sum_eq_selected :=
    inputSurface_ckmTableSum_eq_selected
  input_ckm_factors :=
    inputSurface_ckmFactors_forced
  input_ckm_depth_eq_matrix :=
    inputSurface_ckmDepth_eq_matrixDepth_int
  input_ckm_depth_eq_matrix_object :=
    inputSurface_ckmDepth_eq_matrixObjectDepth_int
  input_ckm_exact_raw_phase_eq_matrix :=
    inputSurface_ckmExactRawPhase_eq_matrix

end StandardModelConstraint
end SaturationMonoid
