import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Wave
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
local instance wholeWavePriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualWholeSourceComplement (h : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.completeSource observation nontrivial half h -
    actualWholeWaveSource observation nontrivial half h

def actualWholeComplementR (h : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (actualWholeSourceComplement observation nontrivial half h)
def actualWholeComplementPairedR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.paired (actualWholeComplementR observation nontrivial half h)
def actualWholeComplementSiblingR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.sibling (actualWholeComplementR observation nontrivial half h)

theorem actual_whole_source_R_wave_complement (h : ℝ) :
    OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) =
      actualWholeWaveR observation nontrivial half h + actualWholeComplementR observation nontrivial half h := by
  unfold actualWholeComplementR actualWholeSourceComplement actualWholeWaveR
  rw [map_sub]
  simp only [OriginalKCombCofinalRAction.original_R_direct]
  module

theorem actual_whole_response_wave_complement (h : ℝ) :
    OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h =
      actualWholeWavePairedR observation nontrivial half h + actualWholeComplementPairedR observation nontrivial half h ∧
    OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h =
      actualWholeWaveSiblingR observation nontrivial half h + actualWholeComplementSiblingR observation nontrivial half h := by
  unfold OriginalKFullSourceRResponse.pairedResponse OriginalKFullSourceRResponse.siblingResponse
    actualWholeWavePairedR actualWholeWaveSiblingR actualWholeComplementPairedR actualWholeComplementSiblingR
  rw [actual_whole_source_R_wave_complement]
  unfold OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
  simp only [map_add]
  constructor <;> module

/-- The mixed fee retains the full actual complement R action, including every Pa correction. -/
def actualWholeMixedWaveSourcePrice (h : ℝ) : ℂ :=
  inner ℂ (actualWholeComplementPairedR observation nontrivial half h)
    (actualWholeWaveSource observation nontrivial half h + fourierL2 (actualWholeWaveSource observation nontrivial half h)) +
  inner ℂ (actualWholeWaveSource observation nontrivial half h - fourierL2 (actualWholeWaveSource observation nontrivial half h))
    (actualWholeComplementSiblingR observation nontrivial half h)

/-- The literal whole physical wave cotest consumes the newly generated diagonal price and keeps the actual same-source mixed fee. -/
theorem actual_whole_wave_cotest_source_price (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualWholeWaveCotest observation nontrivial half h nonnegative bounded =
      actualWholeWaveDiagonalPrice observation nontrivial half h +
      actualWholeMixedWaveSourcePrice observation nontrivial half h := by
  let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  let wave := OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded
  let face := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  have pairRead := face.inner_orthogonalProjectionOnto_eq_of_mem_right (wave + Fphysical wave)
    (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
  have siblingRead := face.inner_orthogonalProjectionOnto_eq_of_mem_left (wave - Fphysical wave)
    (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)
  unfold actualWholeWaveCotest
  dsimp only
  change inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (wave + Fphysical wave) = inner ℂ (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
        ((wave + Fphysical wave : BurnolPaAmbientCarrier) : BurnolL2) at pairRead
  change inner ℂ (wave - Fphysical wave)
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) =
      inner ℂ ((wave - Fphysical wave : BurnolPaAmbientCarrier) : BurnolL2)
        (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) at siblingRead
  rw [pairRead, siblingRead]
  have decomposition := actual_whole_response_wave_complement observation nontrivial half h
  rw [decomposition.1, decomposition.2]
  unfold actualWholeWaveDiagonalPrice actualWholeMixedWaveSourcePrice
  change inner ℂ (actualWholeWavePairedR observation nontrivial half h + actualWholeComplementPairedR observation nontrivial half h)
      (actualWholeWaveSource observation nontrivial half h + fourierL2 (actualWholeWaveSource observation nontrivial half h)) +
    inner ℂ (actualWholeWaveSource observation nontrivial half h - fourierL2 (actualWholeWaveSource observation nontrivial half h))
      (actualWholeWaveSiblingR observation nontrivial half h + actualWholeComplementSiblingR observation nontrivial half h) = _
  simp only [inner_add_left, inner_add_right]
  ring

theorem actual_whole_wave_quadratic_cotest_price (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualWholeWaveCotest observation nontrivial half h nonnegative bounded =
    -2 * (observation.coordinate/2-1/4) *
      inner ℂ (actualWholeWavePairedR observation nontrivial half h)
        (actualWholeWavePairedR observation nontrivial half h) -
    2 * star (observation.coordinate/2-1/4) *
      inner ℂ (actualWholeWaveSiblingR observation nontrivial half h)
        (actualWholeWaveSiblingR observation nontrivial half h) +
    actualWholeMixedWaveSourcePrice observation nontrivial half h := by
  rw [actual_whole_wave_cotest_source_price, actual_whole_wave_diagonal_source_price]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
