import H0mework.Versions.Y.Arithmetic.RieszSynthesis.SynthesisSource
import H0mework.Versions.Y.Arithmetic.RieszSynthesis.WholeRead
import H0mework.Versions.Y.Arithmetic.RieszSynthesis.Defect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteColumns OriginalRieszFiniteSource
noncomputable section

local instance wholeSynthesisAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def wholeSynthesis (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolPaAmbientCarrier :=
  mobiusAdjoint (burnolAnnulusSamplingL2 (positionColumn coordinate shift) 0) +
    gapMeanAdjoint (∫ x : ℝ, positionColumn coordinate shift x) +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (mobiusAdjoint (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0) +
        gapMeanAdjoint (∫ x : ℝ, fourierColumn coordinate shift x))

theorem wholeSynthesis_read (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (wholeSynthesis coordinate shift) value = wholeSourceRead coordinate shift value := by
  have sourceRead (source : BurnolL2) (target : BurnolPaAmbientCarrier) :
      inner ℂ (mobiusAdjoint source) target = inner ℂ source (burnolMobiusSourceL2 target) := by
    rw [mobiusAdjoint_eq]
    exact burnolMobiusSourceL2.adjoint_inner_left target source
  have meanRead (mean : ℂ) (target : BurnolPaAmbientCarrier) :
      inner ℂ (gapMeanAdjoint mean) target =
        star mean * burnolConstantGapCoefficient burnolUnscaledCommonGapRadius target := by
    rw [gapMeanAdjoint_eq, ContinuousLinearMap.adjoint_inner_left]
    simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]
  unfold wholeSynthesis wholeSourceRead
  simp only [inner_add_left, fourier_pairing, sourceRead, meanRead]
  ring

theorem wholeSynthesis_keeps_defect (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    wholeSynthesis coordinate shift = sourceSynthesis coordinate shift +
      defectTranspose (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0) := by
  have emitted (source : BurnolL2) : defectTranspose source =
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius (mobiusAdjoint source) -
        mobiusAdjoint (burnolTateReciprocalL2 source) := rfl
  rw [emitted]
  simp only [wholeSynthesis, sourceSynthesis, map_add]
  module

theorem wholeSynthesis_eq_projection (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) :
    wholeSynthesis coordinate shift = burnolEvenAmbientProjection (forcingIntegral coordinate shift) := by
  apply ext_inner_right ℂ
  intro value
  have projected : inner ℂ (burnolEvenAmbientProjection (forcingIntegral coordinate shift)) value =
      inner ℂ (forcingIntegral coordinate shift) (value : BurnolL2) :=
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
      ).inner_orthogonalProjectionOnto_eq_of_mem_right value _
  rw [wholeSynthesis_read, projected]
  exact (forcing_wholeSourceRead coordinate shift bounded value).symm

/-- The original K and the explicit finite source programme generate the whole boundary. -/
def boundarySource (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolPaAmbientCarrier :=
  (pairedMellinTranslationCharacter coordinate.value shift -
    pairedMellinTranslationCharacter (star coordinate.value) shift) •
      burnolCompletedMellinRieszVector coordinate -
    (1 / 2 : ℂ) • (wholeSynthesis coordinate shift + wholeSynthesis coordinate (-shift))

theorem boundarySource_eq_original (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    boundarySource coordinate shift = burnolZeroPairedFixedAnnulusBoundary coordinate zero shift := by
  rw [OriginalRieszFiniteSource.original_boundary, boundarySource,
    wholeSynthesis_eq_projection coordinate shift bounded,
    wholeSynthesis_eq_projection coordinate (-shift) (by simpa only [abs_neg] using bounded), map_add]

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
