import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Price

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
local instance nonPaCharacterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half





open OriginalKWholePaSourceRankAction
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "z" => observation.coordinate / 2 - 1 / 4

private theorem original_physical_Q_right (x : BurnolL2) (k : BurnolPaOrthogonalCarrier) :
    inner ℂ (P x) (k : BurnolPaAmbientCarrier) = inner ℂ (Q x) (k : BurnolPaAmbientCarrier) :=
  (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_right k (P x)).symm

private theorem original_physical_Q_left (x : BurnolL2) (k : BurnolPaOrthogonalCarrier) :
    inner ℂ (k : BurnolPaAmbientCarrier) (P x) = inner ℂ (k : BurnolPaAmbientCarrier) (Q x) :=
  (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left k (P x)).symm

/-- The only right/left cotests are the original K/FK source-owned Pa-orthogonal faces. -/
theorem actual_nonPa_kernel_cross_original_read (h : ℝ) :
    actualNonPaKernelCross observation nontrivial half h =
      actualOriginalCrossFactor observation h * actualNonPaPairKernelPrice observation nontrivial half h +
      star (actualOriginalCrossFactor observation h) * actualNonPaSiblingKernelPrice observation nontrivial half h := by
  let k : BurnolPaOrthogonalCarrier := ⟨burnolCompletedMellinRieszVector c,
    riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩
  let fk : BurnolPaOrthogonalCarrier := ⟨Fphysical (burnolCompletedMellinRieszVector c),
    (burnolCompactCoPoissonActionSquare.orthogonalAction k).property⟩
  have left := original_physical_Q_right (actualNonPaPairedR observation nontrivial half h) (k+fk)
  have right := original_physical_Q_left (actualNonPaSiblingR observation nontrivial half h) (k-fk)
  unfold actualNonPaKernelCross actualNonPaPairKernelPrice actualNonPaSiblingKernelPrice
    OriginalKPairedResponseGramAction.originalPairKernelRead OriginalKPairedResponseGramAction.originalSiblingKernelRead
  dsimp only
  simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]
  change inner ℂ (P (actualNonPaPairedR observation nontrivial half h))
    (burnolCompletedMellinRieszVector c + Fphysical (burnolCompletedMellinRieszVector c)) = _ at left
  change inner ℂ (burnolCompletedMellinRieszVector c - Fphysical (burnolCompletedMellinRieszVector c))
    (P (actualNonPaSiblingR observation nontrivial half h)) = _ at right
  rw [left,right]
  rfl

def actualWholePaUnitCrossPrice (h : ℝ) : ℂ :=
  actualOriginalCrossFactor observation h * star (actualWholePaSourceCoefficient observation nontrivial half h / 2) *
    actualWholePaUnitPairPrice observation nontrivial half +
  star (actualOriginalCrossFactor observation h) * (actualWholePaSourceCoefficient observation nontrivial half h / 2) *
    actualWholePaUnitSiblingPrice observation nontrivial half

/-- Original Cross directly consumes the paid full-Pa rank and the new nonPa source Ward. -/
theorem actual_original_cross_rank_nonPa_inventory (h : ℝ) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualWholePaUnitCrossPrice observation nontrivial half h + actualNonPaKernelCross observation nontrivial half h := by
  rw [actual_original_cross_consumes_whole_Pa_rank_source,actual_nonPa_kernel_cross_original_read]
  unfold actualWholePaUnitCrossPrice actualWholePaRankSourceCharacter
  ring

def actualNonPaSourceCharacter (h : ℝ) : ℂ :=
  actualWholePaUnitCrossPrice observation nontrivial half h +
    actualNonPaBoundarySourcePrice observation nontrivial half h +
    2*z*inner ℂ (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaPairedR observation nontrivial half h)) +
    2*star z*inner ℂ (P (actualNonPaSiblingR observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) +
    2*actualNonPaOutsideFlux observation nontrivial half h

/-- All Pa/mixed response inventory is now generated into original unit prices, leaving the exact nonPa physical/outside and source boundary fees. -/
theorem actual_original_cross_consumes_nonPa_source_action (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualNonPaSourceCharacter observation nontrivial half h := by
  have source := actual_nonPa_physical_source_Ward observation nontrivial half h nonnegative bounded
  rw [actual_nonPa_boundary_source_price observation nontrivial half h nonnegative bounded] at source
  rw [actual_original_cross_rank_nonPa_inventory]
  unfold actualNonPaSourceCharacter
  linear_combination -2 * source

theorem actual_current_consumes_nonPa_source_action (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
      actualNonPaSourceCharacter observation nontrivial half h := by
  have source := OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action observation nontrivial half h nonnegative bounded n
  rw [actual_original_cross_consumes_nonPa_source_action observation nontrivial half h nonnegative bounded] at source
  exact source.symm

theorem actual_nonPa_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded) atTop
      (𝓝 (actualNonPaSourceCharacter observation nontrivial half h)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_consumes_nonPa_source_action observation nontrivial half h nonnegative bounded] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNonPaSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
