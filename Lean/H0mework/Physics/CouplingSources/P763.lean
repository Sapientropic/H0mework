import H0mework.Physics.MixingSources.P761
import H0mework.Physics.RunningSources.P762

/-!
# Proposition 763: physicalized SU(7) numerical producer spine

P762 welds the concrete SU(7) representation/trace layer to the QCD RG slope.
P759/P761 weld the same SU(7) producer surface to the nine Yukawa depths and
the CKM/Jarlskog phase-depth matrix.

This file packages those two producer axes into one spine.  It is intentionally
kept out of `GrandProducerCompleteness.lean`: the theorem is small, independent,
and gives the downstream inventory a stable producer object to cite.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-- The current finite SU(7) physical producer spine.

It says one concrete finite source surface supplies both:

* the QCD one-loop inverse-flow slope `b0 = 7`;
* the nine Yukawa depths and the CKM/Jarlskog matrix sum `386`.
-/
structure SU7PhysicalizedNumericalProducerSpineCertificate : Prop where
  representation_rg :
    SU7RepresentationPhysicalizedRGFlowProducerCertificate
  yukawa_ckm :
    Nonempty SU7YukawaCKMProducerCertificate
  ckm_matrix :
    Nonempty CKMPhaseDepthMatrixProducerCertificate
  qcd_b0_from_representation :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7
  qcd_inverse_flow_slope_from_representation :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .colorSU3 sigma0 t =
        (1 : ℝ) / sigma0 +
          ((betaCoeff qcdBlockIncidenceOneLoopInput : ℚ) : ℝ) * t
  selected_yukawa_surface :
    SU7PrimitiveYukawaDepthProducerSurface selectedYukawaDepthTableCandidate
  yukawa_surface_iff_selected :
    ∀ T : YukawaDepthTableCandidate,
      SU7PrimitiveYukawaDepthProducerSurface T ↔
        T = selectedYukawaDepthTableCandidate
  nine_yukawa_depths :
    selectedYukawaDepthTableCandidate.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum_from_yukawa :
    ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
      (ckmCPDepthSum : Int)
  ckm_table_sum_from_yukawa :
    ckmDepthSum_fromYukawaDepthTable selectedYukawaDepthTableCandidate =
      (ckmCPDepthSum : Int)
  ckm_matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  ckm_matrix_depth_sum :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)
  ckm_matrix_agrees_yukawa_table :
    ckmJarlskogDepthFromMatrix =
      ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate
  qcd_and_ckm_spine_summary :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)

/-- THEOREM: the physicalized SU(7) representation producer and the
Yukawa/CKM finite producer are the same numerical spine. -/
theorem su7PhysicalizedNumericalProducerSpineCertificate :
    SU7PhysicalizedNumericalProducerSpineCertificate where
  representation_rg :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate
  yukawa_ckm :=
    ⟨su7YukawaCKMProducerCertificate⟩
  ckm_matrix :=
    ⟨ckmPhaseDepthMatrixProducerCertificate⟩
  qcd_b0_from_representation :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.representation_qcd_b0
  qcd_inverse_flow_slope_from_representation :=
    su7RepresentationPhysicalizedRGFlowProducerCertificate.qcd_inverse_flow_slope_from_representation
  selected_yukawa_surface :=
    su7YukawaCKMProducerCertificate.selected_surface
  yukawa_surface_iff_selected :=
    su7YukawaCKMProducerCertificate.surface_iff_selected
  nine_yukawa_depths :=
    su7YukawaCKMProducerCertificate.nine_depths
  ckm_depth_sum_from_yukawa :=
    su7YukawaCKMProducerCertificate.ckm_depth_sum
  ckm_table_sum_from_yukawa :=
    su7YukawaCKMProducerCertificate.ckm_table_sum
  ckm_matrix_rows :=
    ckmPhaseDepthMatrixProducerCertificate.matrix_rows
  ckm_matrix_depth_sum :=
    ckmPhaseDepthMatrixProducerCertificate.jarlskog_depth
  ckm_matrix_agrees_yukawa_table :=
    ckmPhaseDepthMatrixProducerCertificate.jarlskog_agrees_selected_table
  qcd_and_ckm_spine_summary :=
    ⟨su7RepresentationPhysicalizedRGFlowProducerCertificate.representation_qcd_b0,
      su7YukawaCKMProducerCertificate.nine_depths,
      ckmPhaseDepthMatrixProducerCertificate.jarlskog_depth⟩

end StandardModelConstraint
end SaturationMonoid
