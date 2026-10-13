import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Character
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance paCountingClosureComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

theorem actual_Pa_counting_character_error_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualPaCountingCharacterError observation nontrivial half h nonnegative bounded) atTop (𝓝 0) :=by
 unfold actualPaCountingCharacterError
 simpa only [mul_zero] using (actual_Pa_counting_response_error_tendsto c
  (actualWaveSource observation nontrivial half h nonnegative bounded)).const_mul
   ((‖(2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
     (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
     ((star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*
      (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c))*
     OriginalKSourceScaledMaximalResponse.Return.sourceA observation‖*‖K c+Fphysical (K c)‖)+
    ‖star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
     (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
     ((star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*
      (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c))*
     OriginalKSourceScaledMaximalResponse.Return.sourceA observation‖*‖K c-Fphysical (K c)‖)

theorem actual_Pa_counting_character_residual_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded) atTop (𝓝 0) :=by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 exact squeeze_zero (fun n=>norm_nonneg _)
  (actual_Pa_counting_character_residual_error observation nontrivial half h nonnegative bounded)
  (actual_Pa_counting_character_error_tendsto observation nontrivial half h nonnegative bounded)

/-- The independent original character consumes the actual PaWave source action and controlled original counting origin with its unchanged target and inventories. -/
theorem actual_finite_Pa_counting_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded) atTop
  (𝓝 (OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h)) :=by
 have prior:=OriginalKPrimitivePhysicalSourceAction.actual_finite_primitive_character_tendsto observation nontrivial half h nonnegative bounded
 have source:=prior.sub (actual_Pa_counting_character_residual_tendsto observation nontrivial half h nonnegative bounded)
 have actual:(fun n=>OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded n-
  actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n)=
  actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded :=by
  funext n
  have effect:=actual_current_Pa_counting_character_residual observation nontrivial half h nonnegative bounded n
  linear_combination effect
 rw [actual] at source
 simpa only [sub_zero] using source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
