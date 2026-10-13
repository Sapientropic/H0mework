import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance forcingCofinalSourcePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace Paid
export OriginalKFullKernelCofinalSource
 (actualFiniteWholeKernelSource actualWholeKernelSourceResidual actualWholeKernelSourceError
  actual_original_whole_kernel_source_residual actual_original_whole_kernel_source_error
  actual_original_whole_kernel_source_tendsto actual_whole_kernel_error_tendsto)
end Paid

/-- The existing original dilation action is applied to the actual forcing-generated whole ambient material. -/
def actualFiniteForcingField (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):BurnolL2:=
 (2:ℂ) • (pairedBurnolMultiplicativeDilation h (Paid.actualFiniteWholeKernelSource c n)-
  pairedMellinTranslationCharacter (star c.value) h • Paid.actualFiniteWholeKernelSource c n)

def actualForcingFieldResidual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):BurnolL2:=
 (2:ℂ) • (pairedBurnolMultiplicativeDilation h (Paid.actualWholeKernelSourceResidual c n)-
  pairedMellinTranslationCharacter (star c.value) h • Paid.actualWholeKernelSourceResidual c n)

/-- The actual two original action receipts generate the complete forcing field identity. -/
theorem actual_original_forcing_field_receipt (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)=
 (2:ℂ) • (pairedBurnolMultiplicativeDilation h (K c:BurnolL2)-
  pairedMellinTranslationCharacter (star c.value) h • (K c:BurnolL2)) :=by
 unfold pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply]
 change _=(2:ℂ) • ((1/2:ℂ) • (burnolMultiplicativeDilation h (K c:BurnolL2)+
  burnolMultiplicativeDilation (-h) (K c:BurnolL2))-
  pairedMellinTranslationCharacter (star c.value) h • (K c:BurnolL2))
 rw [OriginalRieszFiniteSource.original_finite_action,OriginalRieszFiniteSource.original_finite_action]
 unfold pairedMellinTranslationCharacter
 rw [reciprocalMellinTranslationCharacter_eq_negativeShift]
 module

/-- The actual original source action receipt generates the exact forcing discrepancy, before any Gram or price read. -/
theorem actual_original_forcing_field_residual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)-
 actualFiniteForcingField c h n=actualForcingFieldResidual c h n :=by
 rw [actual_original_forcing_field_receipt]
 have material:=Paid.actual_original_whole_kernel_source_residual c n
 unfold actualForcingFieldResidual
 rw [←material,map_sub]
 unfold actualFiniteForcingField
 module

/-- The full forcing field is obtained from the original source programme and existing action continuity. -/
theorem actual_original_forcing_field_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualFiniteForcingField c h) atTop
  (𝓝 (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))) :=by
 have generated:=((((pairedBurnolMultiplicativeDilation h).continuous.tendsto _).comp
  (Paid.actual_original_whole_kernel_source_tendsto c)).sub
  ((Paid.actual_original_whole_kernel_source_tendsto c).const_smul (pairedMellinTranslationCharacter (star c.value) h))).const_smul (2:ℂ)
 rw [←actual_original_forcing_field_receipt] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
