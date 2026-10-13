import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Control
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance paCountingEffectComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q

/-- The complete original Pa correction is projected only after actual R, with its source coefficient and born unit counting material preserved. -/
theorem actual_original_Pa_R_Q_source (c:BurnolCompletedMellinCoordinate)
 (p:BurnolPaAmbientCarrier) (inPa:p∈burnolCompactCoPoissonClosedRange):
 Q (burnolDirectRightResolvent (c.value/2) (p:BurnolL2))=
 burnolPaResolventSourceCoefficient c p • Q (burnolUnitTailResponse c 4) :=by
 obtain ⟨correction,member,actual⟩:=Submodule.mem_map.mp (burnolPaResolvent_source_correction c p inPa)
 have same:burnolDirectRightResolvent (c.value/2) (p:BurnolL2)=
  (correction:BurnolL2)+burnolPaResolventSourceCoefficient c p • burnolUnitTailResponse c 4 :=
  sub_eq_iff_eq_add.mp actual.symm
 have physical:P (correction:BurnolL2)=correction:=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 have zero:Q (correction:BurnolL2)=0:=by
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (P (correction:BurnolL2))=0
  rw [physical]
  exact Submodule.starProjection_orthogonal_apply_eq_zero member
 rw [same,map_add,map_smul,zero,zero_add]

def actualFinitePaCountingResponse (c:BurnolCompletedMellinCoordinate) (p:BurnolPaAmbientCarrier) (n:Nat):BurnolPaAmbientCarrier:=
 burnolPaResolventSourceCoefficient c p • Q (actualFiniteCountingUnitSource c (actualCountingCutoff n))

def actualPaCountingResponseResidual (c:BurnolCompletedMellinCoordinate) (p:BurnolPaAmbientCarrier) (n:Nat):BurnolPaAmbientCarrier:=
 burnolPaResolventSourceCoefficient c p • Q (actualCountingOriginResidual c (actualCountingCutoff n))

/-- Actual Pa R source and the whole counting actor update generate the full same-source response effect before prices. -/
theorem actual_original_Pa_counting_response_residual (c:BurnolCompletedMellinCoordinate)
 (p:BurnolPaAmbientCarrier) (inPa:p∈burnolCompactCoPoissonClosedRange) (n:Nat):
 Q (burnolDirectRightResolvent (c.value/2) (p:BurnolL2))-actualFinitePaCountingResponse c p n=
 actualPaCountingResponseResidual c p n :=by
 rw [actual_original_Pa_R_Q_source c p inPa]
 have origin:=actual_original_counting_source_residual c _
  (actual_counting_cutoff_source n).1 (actual_counting_cutoff_source n).2.1
 have generated:=congrArg (fun value:BurnolL2=>burnolPaResolventSourceCoefficient c p • Q value) origin
 rw [map_sub,smul_sub] at generated
 exact generated

def actualPaCountingResponseError (c:BurnolCompletedMellinCoordinate) (p:BurnolPaAmbientCarrier) (n:Nat):ℝ:=
 ‖burnolPaResolventSourceCoefficient c p‖*‖Q‖*actualCountingSourceError c (actualCountingCutoff n)

/-- Actual composed Pa face norm pays the full source response residue, with no positive physical margin transfer. -/
theorem actual_original_Pa_counting_response_error (c:BurnolCompletedMellinCoordinate)
 (p:BurnolPaAmbientCarrier) (inPa:p∈burnolCompactCoPoissonClosedRange) (n:Nat):
 ‖Q (burnolDirectRightResolvent (c.value/2) (p:BurnolL2))-actualFinitePaCountingResponse c p n‖≤actualPaCountingResponseError c p n :=by
 rw [actual_original_Pa_counting_response_residual c p inPa]
 unfold actualPaCountingResponseResidual actualPaCountingResponseError
 rw [norm_smul]
 have source:=actual_counting_origin_error c _ (actual_counting_cutoff_source n).1
 have face:‖Q (actualCountingOriginResidual c (actualCountingCutoff n))‖≤
  ‖Q‖*actualCountingSourceError c (actualCountingCutoff n):=
  ((Q).le_opNorm _).trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))
 exact (mul_le_mul_of_nonneg_left face (norm_nonneg _)).trans_eq (by ring)

theorem actual_Pa_counting_response_error_tendsto (c:BurnolCompletedMellinCoordinate) (p:BurnolPaAmbientCarrier):
 Tendsto (actualPaCountingResponseError c p) atTop (𝓝 0) :=by
 unfold actualPaCountingResponseError
 simpa only [mul_zero,mul_assoc] using (actual_counting_source_error_tendsto c).const_mul
  (‖burnolPaResolventSourceCoefficient c p‖*‖Q‖)

/-- The same full actual Pa source response consumes its original counting source closure after R/Q; no new source controller or receiver occurrence is supplied. -/
theorem actual_original_Pa_counting_response_tendsto (c:BurnolCompletedMellinCoordinate)
 (p:BurnolPaAmbientCarrier) (inPa:p∈burnolCompactCoPoissonClosedRange):
 Tendsto (actualFinitePaCountingResponse c p) atTop
  (𝓝 (Q (burnolDirectRightResolvent (c.value/2) (p:BurnolL2)))) :=by
 have source:=((((Q).continuous.tendsto _).comp (actual_original_counting_source_tendsto c)).const_smul
  (burnolPaResolventSourceCoefficient c p))
 rw [←actual_original_Pa_R_Q_source c p inPa] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
