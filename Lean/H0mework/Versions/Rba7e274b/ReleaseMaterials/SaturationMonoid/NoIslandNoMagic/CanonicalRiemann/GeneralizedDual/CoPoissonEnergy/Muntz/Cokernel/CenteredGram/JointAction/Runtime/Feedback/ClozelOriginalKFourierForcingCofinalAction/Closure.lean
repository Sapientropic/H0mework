import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierForcingCofinalAction.Character
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
local instance forcingCofinalClosurePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

theorem actual_Fourier_forcing_price_residual_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualFourierForcingPriceResidual c h) atTop (𝓝 0) :=by
 have constant:Tendsto (fun _:Nat=>inner ℂ (fourierL2 (K c:BurnolL2))
  (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))) atTop
  (𝓝 (inner ℂ (fourierL2 (K c:BurnolL2))
   (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)))):=tendsto_const_nhds
 simpa only [actual_original_Fourier_forcing_price_residual,sub_self] using
  constant.sub (actual_original_Fourier_forcing_price_tendsto c h)

theorem actual_forcing_character_residual_tendsto (h:ℝ):
 Tendsto (actualForcingCharacterResidual observation nontrivial half h) atTop (𝓝 0) :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 have paid:=actual_Fourier_forcing_price_residual_tendsto c h
 have source:=(paid.star.const_mul (w*χ*star a)).add (paid.const_mul (w*star χ*a))
 unfold actualForcingCharacterResidual
 simpa only [mul_zero,star_zero,add_zero] using source

/-- The independent original character consumes the actual finite forcing action together with the two already-generated source programmes. -/
theorem actual_finite_forcing_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded) atTop
  (𝓝 (OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h)) :=by
 have prior:=OriginalKFullKernelCofinalSource.actual_double_source_character_tendsto observation nontrivial half h nonnegative bounded
 have paid:=prior.sub (actual_forcing_character_residual_tendsto observation nontrivial half h)
 have actual:(fun n=>OriginalKFullKernelCofinalSource.actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded n-
  actualForcingCharacterResidual observation nontrivial half h n)=
  actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded :=by
  funext n
  have source:=actual_current_forcing_character_residual observation nontrivial half h nonnegative bounded n
  linear_combination source
 rw [actual] at paid
 simpa only [sub_zero] using paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
