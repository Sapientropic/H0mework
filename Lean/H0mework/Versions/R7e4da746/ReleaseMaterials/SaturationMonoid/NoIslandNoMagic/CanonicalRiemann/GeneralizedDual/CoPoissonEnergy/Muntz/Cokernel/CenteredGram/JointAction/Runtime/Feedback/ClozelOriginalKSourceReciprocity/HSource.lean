import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ReciprocalSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceReciprocity

open Complex MeasureTheory BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKSourceFiniteUpdate
open scoped InnerProductSpace
noncomputable section

local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem reciprocal_generatedK_H (c : BurnolCompletedMellinCoordinate) :
    sourceReciprocity c (generatedK c) =
      -fourierL2 (generatedK c + sourceRate c • sourceAdjointField c) := by
  have evenK : reflectL2 (generatedK c) = generatedK c := by
    rw [generatedK_eq_original]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have right : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have actual : sourceResolvent c (fourierL2 (generatedK c)) =
      fourierL2 (sourceAdjointField c) := by
    apply fourierL2.injective
    rw [fourierL2_fourierL2, h_source_even]
    change fourierL2 (burnolDirectRightResolvent (star c.value/2)
      (fourierL2 (generatedK c))) = sourceAdjointField c
    rw [FiniteMobiusResolventFlux.fourier_R _ right, fourierL2_fourierL2, evenK]
    change sourceAdjoint c (generatedK c) = sourceAdjointField c
    rw [generatedK_eq_original, sourceAdjoint_original]
  rw [sourceReciprocity_apply, actual, map_add, map_smul]
  module

/-- The new source action consumes all paid H faces, including its actual outside cost. -/
theorem reciprocal_K_full_inventory (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    (burnolEvenAmbientProjection (sourceReciprocity c (generatedK c)) : BurnolL2) =
        -fourierL2 (generatedK c + sourceRate c • hPhysicalField c) ∧
    (OriginalKCombCofinalPaAction.E (sourceReciprocity c (generatedK c)) : BurnolL2) =
        -sourceRate c • fourierL2 (paAdjointSource c : BurnolL2) ∧
    (OriginalKCombCofinalPaAction.Q (sourceReciprocity c (generatedK c)) : BurnolL2) =
        -fourierL2 (generatedK c + sourceRate c • hQField c) ∧
    sourceReciprocity c (generatedK c) -
        (burnolEvenAmbientProjection (sourceReciprocity c (generatedK c)) : BurnolL2) =
        -sourceRate c • fourierL2 (hQuarterAmplitude c • hPowerPhysicalCorrection c) ∧
    ‖sourceReciprocity c (generatedK c)‖^2 -
        ‖(burnolEvenAmbientProjection (sourceReciprocity c (generatedK c)) : BurnolL2)‖^2 =
        ‖sourceRate c‖^2 * ‖hQuarterAmplitude c‖^2 * ‖hPowerPhysicalCorrection c‖^2 := by
  let P := burnolEvenAmbientProjection
  let E := OriginalKCombCofinalPaAction.E
  let Q := OriginalKCombCofinalPaAction.Q
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  have PF (v : BurnolL2) : (P (fourierL2 v) : BurnolL2) = fourierL2 (P v : BurnolL2) :=
    (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius v).symm
  have full (v : BurnolL2) : (E v : BurnolL2) + (Q v : BurnolL2) = (P v : BurnolL2) :=
    congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2))
      (Submodule.starProjection_add_starProjection_orthogonal
        (K := burnolCompactCoPoissonClosedRange.toSubmodule) (P v))
  have QF (v : BurnolL2) : (Q (fourierL2 v) : BurnolL2) = fourierL2 (Q v : BurnolL2) := by
    have physical : P (fourierL2 v) = F (P v) := by
      apply Subtype.ext
      exact PF v
    change (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection (P (fourierL2 v)) : BurnolL2) = _
    rw [show P (fourierL2 v) = F (P v) from physical]
    have natural := congrArg
      (fun result : SourceGeneratedHilbertCokernel.OrthogonalResidual burnolCompactCoPoissonLanding =>
        ((result : BurnolPaAmbientCarrier) : BurnolL2))
      (burnolCompactCoPoissonActionSquare.orthogonalAction_residual (P v))
    exact natural.symm
  have EF (v : BurnolL2) : (E (fourierL2 v) : BurnolL2) = fourierL2 (E v : BurnolL2) := by
    have all := full (fourierL2 v)
    rw [QF, PF] at all
    have transported := congrArg fourierL2 (full v)
    rw [map_add] at transported
    linear_combination (norm := module) all - transported
  have PK : P (generatedK c) = burnolCompletedMellinRieszVector c := by
    rw [generatedK_eq_original]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have EK : E (generatedK c) = 0 := by
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (P (generatedK c)) = 0
    rw [PK]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr orthogonal
  have QK : (Q (generatedK c) : BurnolL2) = generatedK c := by
    have all := full (generatedK c)
    rw [EK, PK] at all
    simpa only [ZeroMemClass.coe_zero, zero_add, generatedK_eq_original] using all
  have projected : (P (sourceReciprocity c (generatedK c)) : BurnolL2) =
      -fourierL2 (generatedK c + sourceRate c • hPhysicalField c) := by
    rw [reciprocal_generatedK_H, map_neg]
    change -(P (fourierL2 _) : BurnolL2) = _
    rw [PF, map_add, map_smul]
    change -fourierL2 ((P (generatedK c) : BurnolL2) + sourceRate c •
      (P (sourceAdjointField c) : BurnolL2)) = _
    rw [PK, hPhysicalField_actual]
    rw [generatedK_eq_original]
  have pa : (E (sourceReciprocity c (generatedK c)) : BurnolL2) =
      -sourceRate c • fourierL2 (paAdjointSource c : BurnolL2) := by
    rw [reciprocal_generatedK_H, map_neg]
    change -(E (fourierL2 _) : BurnolL2) = _
    rw [EF, map_add, map_smul, EK, paAdjointSource_actual c orthogonal]
    simp only [zero_add, SetLike.val_smul, map_smul]
    module
  have qfield : (Q (sourceReciprocity c (generatedK c)) : BurnolL2) =
      -fourierL2 (generatedK c + sourceRate c • hQField c) := by
    rw [reciprocal_generatedK_H, map_neg]
    change -(Q (fourierL2 _) : BurnolL2) = _
    rw [QF, map_add, map_smul]
    change -fourierL2 ((Q (generatedK c) : BurnolL2) + sourceRate c •
      (Q (sourceAdjointField c) : BurnolL2)) = _
    rw [QK, hQField_actual c orthogonal]
  have loss : sourceReciprocity c (generatedK c) -
      (P (sourceReciprocity c (generatedK c)) : BurnolL2) =
      -sourceRate c • fourierL2 (hQuarterAmplitude c • hPowerPhysicalCorrection c) := by
    rw [projected, reciprocal_generatedK_H]
    simp only [map_add, map_smul, hPhysicalField, map_sub]
    module
  have cost : ‖sourceReciprocity c (generatedK c)‖^2 -
      ‖(P (sourceReciprocity c (generatedK c)) : BurnolL2)‖^2 =
      ‖sourceRate c‖^2 * ‖hQuarterAmplitude c‖^2 * ‖hPowerPhysicalCorrection c‖^2 := by
    have perpendicular := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_inner_eq_zero
      (sourceReciprocity c (generatedK c)) (P (sourceReciprocity c (generatedK c)))
      (P (sourceReciprocity c (generatedK c))).property
    change inner ℂ (sourceReciprocity c (generatedK c) -
      (P (sourceReciprocity c (generatedK c)) : BurnolL2))
      (P (sourceReciprocity c (generatedK c)) : BurnolL2) = 0 at perpendicular
    have split := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ perpendicular
    have recovered : sourceReciprocity c (generatedK c) -
        (P (sourceReciprocity c (generatedK c)) : BurnolL2) +
        (P (sourceReciprocity c (generatedK c)) : BurnolL2) =
        sourceReciprocity c (generatedK c) := by module
    rw [recovered, loss] at split
    simp only [←pow_two, norm_neg, norm_smul, fourierL2.norm_map, mul_pow] at split
    linarith
  exact ⟨projected, pa, qfield, loss, cost⟩

end
end OriginalKSourceReciprocity
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
