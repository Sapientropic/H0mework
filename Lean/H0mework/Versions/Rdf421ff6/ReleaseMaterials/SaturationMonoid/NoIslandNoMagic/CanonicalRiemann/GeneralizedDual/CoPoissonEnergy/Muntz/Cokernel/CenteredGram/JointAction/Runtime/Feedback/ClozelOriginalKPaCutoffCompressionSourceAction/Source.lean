import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Complete
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace

/-- Actual support restriction followed by its original zero-extension adjoint. -/
def cutoffAction (radius : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)

/-- The same action compressed on the original ambient face, with no invariant-subspace premise. -/
def physicalCutoffAction (radius : ℝ) : BurnolPaAmbientCarrier →L[ℂ] BurnolPaAmbientCarrier :=
 burnolEvenAmbientProjection.comp ((cutoffAction radius).comp
  (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule))

def physicalTailAction (radius : ℝ) : BurnolPaAmbientCarrier →L[ℂ] BurnolPaAmbientCarrier :=
 ContinuousLinearMap.id ℂ BurnolPaAmbientCarrier - physicalCutoffAction radius

def outsideTailAction (radius : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 ContinuousLinearMap.id ℂ BurnolL2 - cutoffAction radius

theorem cutoff_action_inner (radius : ℝ) (left right : BurnolL2) :
 inner ℂ left (cutoffAction radius right) =
 inner ℂ (burnolRadiusRestriction radius left) (burnolRadiusRestriction radius right) :=
 by
 change inner ℂ left ((burnolRadiusRestriction radius).adjoint (burnolRadiusRestriction radius right)) = _
 exact ContinuousLinearMap.adjoint_inner_right (burnolRadiusRestriction radius) left (burnolRadiusRestriction radius right)

theorem physical_cutoff_action_inner (radius : ℝ) (left right : BurnolPaAmbientCarrier) :
 inner ℂ left (physicalCutoffAction radius right) =
 inner ℂ (burnolRadiusRestriction radius (left : BurnolL2)) (burnolRadiusRestriction radius (right : BurnolL2)) := by
 change inner ℂ left (burnolEvenAmbientProjection (cutoffAction radius right)) = _
 rw [burnolEvenAmbientProjection,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 exact cutoff_action_inner _ _ _

theorem physical_cutoff_action_symmetric (radius : ℝ) :
 (physicalCutoffAction radius).toLinearMap.IsSymmetric := by
 intro left right
 change inner ℂ (burnolEvenAmbientProjection (cutoffAction radius left)) right =
  inner ℂ left (burnolEvenAmbientProjection (cutoffAction radius right))
 rw [burnolEvenAmbientProjection,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 calc
  _ = inner ℂ (burnolRadiusRestriction radius (left : BurnolL2)) (burnolRadiusRestriction radius (right : BurnolL2)) :=
   ContinuousLinearMap.adjoint_inner_left (burnolRadiusRestriction radius) (right : BurnolL2) (burnolRadiusRestriction radius (left : BurnolL2))
  _ = _ := (cutoff_action_inner radius left right).symm

theorem physical_cutoff_action_positive_gram (radius : ℝ) (value : BurnolPaAmbientCarrier) :
 (inner ℂ value (physicalCutoffAction radius value)).re = ‖burnolRadiusRestriction radius (value : BurnolL2)‖^2 := by
 rw [physical_cutoff_action_inner]
 exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm

theorem zero_extension_norm (radius : ℝ) (value : BurnolRadiusIntervalL2 radius) :
 ‖burnolRadiusZeroExtension radius value‖ = ‖value‖ := by
 rw [←burnolRadiusZeroExtensionExplicit_is_adjoint]
 exact burnolRadiusZeroExtensionValue_norm value

theorem restriction_norm_le (radius : ℝ) (value : BurnolL2) :
 ‖burnolRadiusRestriction radius value‖ ≤ ‖value‖ := by
 have norm := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (burnolRadiusRestriction radius) value
 change ‖burnolRadiusRestriction radius value‖^2 = (inner ℂ value (cutoffAction radius value)).re at norm
 have bound := re_inner_le_norm (𝕜:=ℂ) value (cutoffAction radius value)
 change (inner ℂ value (cutoffAction radius value)).re ≤ ‖value‖ * ‖cutoffAction radius value‖ at bound
 have extension := zero_extension_norm radius (burnolRadiusRestriction radius value)
 change ‖cutoffAction radius value‖ = _ at extension
 rw [←norm,extension] at bound
 by_cases zero : ‖burnolRadiusRestriction radius value‖ = 0
 · rw [zero]; exact norm_nonneg _
 · have positive := lt_of_le_of_ne (norm_nonneg (burnolRadiusRestriction radius value)) (Ne.symm zero)
   rw [pow_two] at bound
   exact le_of_mul_le_mul_right bound positive

theorem physical_cutoff_action_contractive (radius : ℝ) (value : BurnolPaAmbientCarrier) :
 ‖physicalCutoffAction radius value‖ ≤ ‖value‖ := by
 calc
  _ ≤ ‖cutoffAction radius value‖ :=
   (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.norm_orthogonalProjectionOnto_apply_le _
  _ = ‖burnolRadiusRestriction radius (value : BurnolL2)‖ := zero_extension_norm _ _
  _ ≤ ‖(value : BurnolL2)‖ := restriction_norm_le _ _
  _ = ‖value‖ := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
