import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Projection

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance nonPaWardSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half




open OriginalKWholePaSourceRankAction
local notation "O" => OriginalKPairedResponseGramAction.originalOutside
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "z" => observation.coordinate / 2 - 1 / 4

private theorem source_physical_gram (x y : BurnolL2) :
    inner ℂ x y = inner ℂ (P x) (P y) + inner ℂ (O x) (O y) := by
  let face := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  have pRead := face.inner_orthogonalProjectionOnto_eq_of_mem_right (P y) x
  change inner ℂ (P x) (P y) = inner ℂ x (P y : BurnolL2) at pRead
  have oRead : inner ℂ (O x) (O y) = inner ℂ x (O y) := by
    unfold OriginalKPairedResponseGramAction.originalOutside
    rw [face.orthogonal.inner_starProjection_left_eq_right]
    rw [Submodule.starProjection_eq_self_iff.mpr (face.orthogonal.starProjection_apply_mem y)]
  have split := face.starProjection_add_starProjection_orthogonal y
  change (P y : BurnolL2) + O y = y at split
  rw [pRead, oRead, ←inner_add_right, split]

/-- Original nonPa source actions first generate their whole unitary balance. -/
theorem actual_nonPa_R_source_Ward (h : ℝ) :
    inner ℂ (actualNonPaPairedR observation nontrivial half h) (actualNonPaSiblingVelocity observation nontrivial half h) +
      inner ℂ (actualNonPaPairedVelocity observation nontrivial half h) (actualNonPaSiblingR observation nontrivial half h) = 0 := by
  have action := actual_Pa_nonPa_R_source_actions observation nontrivial half h
  have generated := action.2.2.1.inner ℂ action.2.2.2
  have fixed : (fun t : ℝ => inner ℂ
      (burnolMultiplicativeDilation (-t/2) (actualNonPaPairedR observation nontrivial half h))
      (burnolMultiplicativeDilation (-t/2) (actualNonPaSiblingR observation nontrivial half h))) =
      fun _ => inner ℂ (actualNonPaPairedR observation nontrivial half h)
        (actualNonPaSiblingR observation nontrivial half h) :=
    funext fun t => (burnolMultiplicativeDilation (-t/2)).inner_map_map _ _
  rw [fixed] at generated
  have source := generated.unique (hasDerivAt_const (0:ℝ) _)
  simpa only [neg_zero,zero_div,burnolMultiplicativeDilation_zero] using source

/-- The projected effect pays the original actual nonPa outside inventory without granting physical membership to nonPa R. -/
theorem actual_nonPa_physical_forcing_effect (h : ℝ) :
    inner ℂ (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaSiblingVelocity observation nontrivial half h)) +
      inner ℂ (P (actualNonPaPairedVelocity observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) =
      -actualNonPaOutsideFlux observation nontrivial half h := by
  have whole := actual_nonPa_R_source_Ward observation nontrivial half h
  rw [source_physical_gram
    (actualNonPaPairedR observation nontrivial half h) (actualNonPaSiblingVelocity observation nontrivial half h),
    source_physical_gram
    (actualNonPaPairedVelocity observation nontrivial half h) (actualNonPaSiblingR observation nontrivial half h)] at whole
  unfold actualNonPaOutsideFlux
  linear_combination whole

def actualNonPaBoundaryCross (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : ℂ :=
  let b := OriginalKPairedResponseGramAction.originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded
  let factor := 2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
  inner ℂ (P (actualNonPaPairedR observation nontrivial half h)) (factor • (b + Fphysical b)) +
    inner ℂ (factor • (b - Fphysical b)) (P (actualNonPaSiblingR observation nontrivial half h))

def actualNonPaKernelCross (h : ℝ) : ℂ :=
  let k := burnolCompletedMellinRieszVector c
  let factor := actualOriginalCrossFactor observation h
  inner ℂ (P (actualNonPaPairedR observation nontrivial half h)) (factor • (k + Fphysical k)) +
    inner ℂ (factor • (k - Fphysical k)) (P (actualNonPaSiblingR observation nontrivial half h))

/-- The already-generated Pa-orthogonal source forcing is consumed by the exact original nonPa physical action, before the target Cross read. -/
theorem actual_nonPa_physical_source_Ward (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    z * inner ℂ (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaPairedR observation nontrivial half h)) +
    star z * inner ℂ (P (actualNonPaSiblingR observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) +
    (1/2:ℂ) * (actualNonPaBoundaryCross observation nontrivial half h nonnegative bounded -
      actualNonPaKernelCross observation nontrivial half h) + actualNonPaOutsideFlux observation nontrivial half h = 0 := by
  have action := actual_nonPa_physical_forcing_effect observation nontrivial half h
  unfold actualNonPaPairedVelocity actualNonPaSiblingVelocity at action
  simp only [map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,
    inner_smul_left,inner_smul_right,starRingEnd_apply] at action
  rw [actual_nonPa_source_fourier,actual_nonPa_source_physical,
    OriginalKPairedResponseGramAction.actual_original_boundary_forcing observation nontrivial half h nonnegative bounded] at action
  unfold actualNonPaBoundaryCross actualNonPaKernelCross actualOriginalCrossFactor
  dsimp only
  simp only [map_sub,map_smul,smul_add,smul_sub,inner_add_right,
    inner_sub_left,inner_sub_right,star_sub,star_div₀,star_one,star_ofNat] at action ⊢
  linear_combination action

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
