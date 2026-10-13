import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitivePhysicalSourceAction.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance primitivePhysicalClosureComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

theorem actual_primitive_character_error_tendsto (h:ℝ):
 Tendsto (actualPrimitiveCharacterError observation nontrivial half h) atTop (𝓝 0) :=by
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let W:=star D*D
 let κ:=Physical.actualResponseKappa c
 let w:=star κ*κ*W
 have k:=OriginalKFourierForcingCofinalAction.actual_Fourier_forcing_price_error_tendsto c h
 have primitive:=actual_primitive_action_error_tendsto observation nontrivial half h
 have source:=((k.const_mul (‖w*χ*star a‖+‖w*star χ*a‖)).add
  ((primitive.const_mul ‖K c+Fphysical (K c)‖).const_mul ‖χ*κ*W*(2*star a)‖)).add
  ((primitive.const_mul ‖K c-Fphysical (K c)‖).const_mul ‖star χ*star κ*W*(2*a)‖)
 unfold actualPrimitiveCharacterError
 simpa only [mul_zero,add_zero] using source

theorem actual_primitive_character_residual_tendsto (h:ℝ):
 Tendsto (actualPrimitiveCharacterResidual observation nontrivial half h) atTop (𝓝 0) :=by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 exact squeeze_zero (fun n=>norm_nonneg _) (actual_primitive_character_residual_error observation nontrivial half h)
  (actual_primitive_character_error_tendsto observation nontrivial half h)

/-- The independent complete original character consumes the generated primitive full action and own K forcing source, using its original unchanged target and kappa-zero scope. -/
theorem actual_finite_primitive_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded) atTop
  (𝓝 (OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h)) :=by
 have prior:=OriginalKFourierForcingCofinalAction.actual_finite_forcing_character_tendsto observation nontrivial half h nonnegative bounded
 have paid:=prior.sub (actual_primitive_character_residual_tendsto observation nontrivial half h)
 have actual:(fun n=>OriginalKFourierForcingCofinalAction.actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded n-
  actualPrimitiveCharacterResidual observation nontrivial half h n)=
  actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded :=by
  funext n
  have source:=actual_current_primitive_character_residual observation nontrivial half h nonnegative bounded n
  linear_combination source
 rw [actual] at paid
 simpa only [sub_zero] using paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
