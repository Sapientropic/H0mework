import H0mework.Versions.V2.Arithmetic.MellinProjection.PaBoundaryCommutator

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

def gapMeanVector : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (burnolAmbientGapRieszVector burnolUnscaledCommonGapRadius)

theorem gapMeanVector_readback (value : BurnolPaAmbientCarrier) :
    inner ℂ gapMeanVector value =
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_right value
      (burnolAmbientGapRieszVector burnolUnscaledCommonGapRadius)
  change inner ℂ gapMeanVector value = _ at projected
  rw [projected, burnolAmbientGapRieszVector_readback]
  rfl

def gapMeanAdjoint : ℂ →L[ℂ] BurnolPaAmbientCarrier :=
  ContinuousLinearMap.toSpanSingleton ℂ gapMeanVector

theorem gapMeanAdjoint_eq :
    gapMeanAdjoint = (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro coefficient value
  change inner ℂ (coefficient • gapMeanVector) value =
    inner ℂ coefficient (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value)
  have scaled := inner_smul_left (𝕜 := ℂ) gapMeanVector value coefficient
  rw [scaled, gapMeanVector_readback]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
