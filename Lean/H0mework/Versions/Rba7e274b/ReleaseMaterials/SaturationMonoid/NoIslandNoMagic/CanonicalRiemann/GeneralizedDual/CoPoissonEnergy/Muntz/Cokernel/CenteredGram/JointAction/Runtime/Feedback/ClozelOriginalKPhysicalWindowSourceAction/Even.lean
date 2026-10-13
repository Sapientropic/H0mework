import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.EvenAction
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.TwinRegularity

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance profileEvenComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


/-- The actual complete original material has its own generated even qualification; no projection membership is transferred to an unrelated value. -/
theorem actual_original_source_even (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    reflectL2 (actualSourceMaterial observation nontrivial half h) =
      actualSourceMaterial observation nontrivial half h := by
  have wave : reflectL2 (OriginalCommonInverseForcing.SourceJoint.upperSourceWave c h) =
      OriginalCommonInverseForcing.SourceJoint.upperSourceWave c h := by
    have qualified := OriginalCommonInverseForcing.SourceJoint.generated_upper_wave_inPa c h nonnegative bounded
    obtain ⟨physical, _, actual⟩ := Submodule.mem_map.mp qualified
    change (physical : BurnolL2) = OriginalCommonInverseForcing.SourceJoint.upperSourceWave c h at actual
    rw [← actual]
    exact mem_evenL2ClosedFace_iff.mp physical.property.2
  have field : reflectL2 (OriginalCommonInverseForcing.SourceJoint.upperSourceField c h) =
      OriginalCommonInverseForcing.SourceJoint.upperSourceField c h := by
    unfold OriginalCommonInverseForcing.SourceJoint.upperSourceField
    exact burnolAmbientEvenPart_even _
  have mean := mem_evenL2ClosedFace_iff.mp
    (OriginalCommonInverseForcing.SourceJoint.FullStock.meanDebt c h).property.2
  unfold actualSourceMaterial OriginalKFullSourceRResponse.completeSource
    OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection
  simp only [map_add, map_sub, map_smul, wave, field]
  rw [mean]

theorem actual_original_R_material_even (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    reflectL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h)) =
    OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h) := by
  let material := actualSourceMaterial observation nontrivial half h
  have original := OriginalPaPhysicalGreen.sourceVolterraResolvent_reflect c (burnolTateReciprocalL2 material)
  have even : reflectL2 material = material := actual_original_source_even observation nontrivial half h nonnegative bounded
  change reflectL2 (burnolTateReciprocalL2 (burnolDirectRightResolvent ((c).value/2)
    (burnolTateReciprocalL2 (burnolTateReciprocalL2 material)))) =
    burnolTateReciprocalL2 (burnolDirectRightResolvent ((c).value/2)
      (burnolTateReciprocalL2 (reflectL2 (burnolTateReciprocalL2 material)))) at original
  rw [burnolTateReciprocalL2_involutive, ← burnolTateReciprocal_reflect,
    ← burnolTateReciprocal_reflect, burnolTateReciprocalL2_involutive, even] at original
  have generated := congrArg burnolTateReciprocalL2 original
  rw [burnolTateReciprocalL2_involutive, burnolTateReciprocalL2_involutive] at generated
  simpa only [OriginalKCombCofinalRAction.original_R_direct,
    OriginalKCombCofinalTwoDirection.coordinate_value] using generated


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
