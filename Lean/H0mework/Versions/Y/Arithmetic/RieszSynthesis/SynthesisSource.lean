import H0mework.Versions.Y.Arithmetic.RieszSynthesis.MobiusAdjoint
import H0mework.Versions.Y.Arithmetic.RieszColumns.ColumnsRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteColumns
noncomputable section

local instance synthesisAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem tate_pairing (left right : BurnolL2) :
    inner ℂ (burnolTateReciprocalL2 left) right = inner ℂ left (burnolTateReciprocalL2 right) := by
  let actual : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    ⟨burnolTateReciprocalL2.toLinearMap, burnolTateReciprocalValue_norm⟩
  have source := actual.inner_map_map left (burnolTateReciprocalL2 right)
  change inner ℂ (burnolTateReciprocalL2 left)
    (burnolTateReciprocalL2 (burnolTateReciprocalL2 right)) = _ at source
  rw [burnolTateReciprocalL2_involutive] at source
  exact source

theorem fourier_pairing (left right : BurnolPaAmbientCarrier) :
    inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left) right =
      inner ℂ left (evenFaceFourierEquiv burnolUnscaledCommonGapRadius right) := by
  have twice : fourierL2 (fourierL2 (right : BurnolL2)) = (right : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp right.property.2
  have actual := fourierL2.inner_map_map (left : BurnolL2) (fourierL2 (right : BurnolL2))
  rw [twice] at actual
  exact actual

/-- Original finite source synthesis, including both mean vectors and the same-source Tate action. -/
def sourceSynthesis (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolPaAmbientCarrier :=
  mobiusAdjoint (burnolAnnulusSamplingL2 (positionColumn coordinate shift) 0) +
    gapMeanAdjoint (∫ x : ℝ, positionColumn coordinate shift x) +
    mobiusAdjoint (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 (fourierColumn coordinate shift) 0)) +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (gapMeanAdjoint (∫ x : ℝ, fourierColumn coordinate shift x))

theorem sourceSynthesis_read (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (sourceSynthesis coordinate shift) value = firstSourceRead coordinate shift value := by
  have sourceRead (source : BurnolL2) :
      inner ℂ (mobiusAdjoint source) value = inner ℂ source (burnolMobiusSourceL2 value) := by
    rw [mobiusAdjoint_eq]
    exact burnolMobiusSourceL2.adjoint_inner_left value source
  have meanRead (mean : ℂ) (target : BurnolPaAmbientCarrier) :
      inner ℂ (gapMeanAdjoint mean) target =
        star mean * burnolConstantGapCoefficient burnolUnscaledCommonGapRadius target := by
    rw [gapMeanAdjoint_eq, ContinuousLinearMap.adjoint_inner_left]
    simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]
  unfold sourceSynthesis firstSourceRead
  simp only [inner_add_left, sourceRead, meanRead, fourier_pairing, tate_pairing]
  ring

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
