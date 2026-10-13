import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
open Complex MeasureTheory BurnolPhysicalState
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance effectPhysicalAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKPairedResponseGramAction.originalOutside

private theorem actual_physical_whole_Gram (x y : BurnolL2) :
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
  rw [pRead, oRead, ← inner_add_right, split]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The true whole source action is consumed before the complete P face; the original outside inventory remains. -/
theorem actual_whole_physical_forcing_flux (h : ℝ) :
    inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (P (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h)) +
    inner ℂ (P (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) =
    -OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h := by
  have whole := OriginalKPairedResponseGramAction.actual_whole_forcing_conserves_gram
    observation nontrivial half h
  rw [actual_physical_whole_Gram
    (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
    (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h),
    actual_physical_whole_Gram
      (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h)
      (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)] at whole
  unfold OriginalKPairedResponseGramAction.actualOutsideFlux
  linear_combination whole

local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualWholePhysicalBoundaryCross (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : ℂ :=
  let boundary := OriginalKPairedResponseGramAction.BoundarySource.generatedBoundary
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded
  let factor := 2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
  inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
    (factor • (boundary + Fphysical boundary)) +
  inner ℂ (factor • (boundary - Fphysical boundary))
    (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))

def actualWholePhysicalKernelCross (h : ℝ) : ℂ :=
  let k := burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
  let factor := 2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
    (pairedMellinTranslationCharacter observation.coordinate h -
      pairedMellinTranslationCharacter (star observation.coordinate) h)
  inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
    (factor • (k + Fphysical k)) +
  inner ℂ (factor • (k - Fphysical k))
    (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))

def actualWholeWaveCotest (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : ℂ :=
  let wave := OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded
  inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
    (wave + Fphysical wave) +
  inner ℂ (wave - Fphysical wave)
    (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))

/-- The actual full physical source action pays the joint Pa boundary/flux inventory without supplying a trace or dropping the same-born wave. -/
theorem actual_whole_physical_source_Ward (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    (observation.coordinate/2-1/4) *
      inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
        (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) +
    star (observation.coordinate/2-1/4) *
      inner ℂ (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
        (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) +
    (1/2 : ℂ) * (actualWholePhysicalBoundaryCross observation nontrivial half h nonnegative bounded -
      actualWholePhysicalKernelCross observation nontrivial half h +
      actualWholeWaveCotest observation nontrivial half h nonnegative bounded) +
    OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h = 0 := by
  have action := actual_whole_physical_forcing_flux observation nontrivial half h
  unfold OriginalKPairedResponseGramAction.pairedVelocity OriginalKPairedResponseGramAction.siblingVelocity at action
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_smul_left, inner_smul_right, starRingEnd_apply] at action
  have fourierFace : P (fourierL2 (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) =
      Fphysical (P (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) := by
    apply Subtype.ext
    exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius _).symm
  rw [fourierFace, actual_whole_physical_source_forcing observation nontrivial half h nonnegative bounded] at action
  unfold actualWholePhysicalBoundaryCross actualWholePhysicalKernelCross actualWholeWaveCotest
  dsimp only
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, star_sub, star_div₀, star_one, star_ofNat] at action ⊢
  linear_combination action

private theorem actual_physical_Q_kernel_right (x : BurnolL2) (k : BurnolPaOrthogonalCarrier) :
    inner ℂ (P x) (k : BurnolPaAmbientCarrier) =
      inner ℂ (OriginalKFullSourceRResponse.Paid.Q x) (k : BurnolPaAmbientCarrier) := by
  have source := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_right k (P x)
  exact source.symm

private theorem actual_physical_Q_kernel_left (x : BurnolL2) (k : BurnolPaOrthogonalCarrier) :
    inner ℂ (k : BurnolPaAmbientCarrier) (P x) =
      inner ℂ (k : BurnolPaAmbientCarrier) (OriginalKFullSourceRResponse.Paid.Q x) := by
  have source := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left k (P x)
  exact source.symm

/-- Both cotests are the original K/FK same-source Pa-orthogonal faces; this does not grant the whole physical wave cotest that qualification. -/
theorem actual_physical_kernel_cross_original (h : ℝ) :
    actualWholePhysicalKernelCross observation nontrivial half h =
      OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h := by
  let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  let k : BurnolPaOrthogonalCarrier := ⟨burnolCompletedMellinRieszVector coordinate,
    riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero⟩
  let fk : BurnolPaOrthogonalCarrier := ⟨Fphysical (burnolCompletedMellinRieszVector coordinate),
    (burnolCompactCoPoissonActionSquare.orthogonalAction k).property⟩
  have left := actual_physical_Q_kernel_right
    (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) (k + fk)
  have right := actual_physical_Q_kernel_left
    (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) (k - fk)
  unfold actualWholePhysicalKernelCross OriginalKPairedResponseGramAction.originalKernelCross
  dsimp only
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply]
  change inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (burnolCompletedMellinRieszVector coordinate + Fphysical (burnolCompletedMellinRieszVector coordinate)) = _ at left
  change inner ℂ (burnolCompletedMellinRieszVector coordinate - Fphysical (burnolCompletedMellinRieszVector coordinate))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) = _ at right
  rw [left, right]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
