import H0mework.Versions.V2.Arithmetic.RieszSynthesis.SynthesisSource
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.WholeRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex
open scoped InnerProductSpace
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The actual Fourier and Tate source routes return their difference through the finite Möbius program. -/
def defectTranspose : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).toContinuousLinearEquiv.toContinuousLinearMap.comp
      mobiusAdjoint -
    mobiusAdjoint.comp burnolTateReciprocalL2

theorem defectTranspose_pairing (source : BurnolL2) (value : BurnolPaAmbientCarrier) :
    inner ℂ (defectTranspose source) value = inner ℂ source (sourceFourierDefect value) := by
  have sourceRead (input : BurnolL2) (target : BurnolPaAmbientCarrier) :
      inner ℂ (mobiusAdjoint input) target = inner ℂ input (burnolMobiusSourceL2 target) := by
    rw [mobiusAdjoint_eq]
    exact burnolMobiusSourceL2.adjoint_inner_left target input
  change inner ℂ
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (mobiusAdjoint source) -
        mobiusAdjoint (burnolTateReciprocalL2 source)) value = _
  simp only [inner_sub_left, fourier_pairing, sourceRead, tate_pairing,
    sourceFourierDefect, inner_sub_right]

theorem defectTranspose_mem_orthogonal (source : BurnolL2) :
    defectTranspose source ∈ burnolPaOrthogonalClosedFace := by
  change defectTranspose source ∈ Submodule.orthogonal burnolCompactCoPoissonClosedRange.toSubmodule
  rw [Submodule.mem_orthogonal']
  intro value inPa
  rw [defectTranspose_pairing, sourceFourierDefect_onPa value inPa, inner_zero_right]

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
