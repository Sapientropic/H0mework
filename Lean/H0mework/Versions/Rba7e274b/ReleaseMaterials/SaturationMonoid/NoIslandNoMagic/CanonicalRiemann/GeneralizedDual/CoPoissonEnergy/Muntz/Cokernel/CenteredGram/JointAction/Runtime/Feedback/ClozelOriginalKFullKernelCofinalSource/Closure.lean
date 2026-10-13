import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance kernelCofinalClosurePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

/-- Current original character read consumes its literal FK price effect, before either source limit is taken. -/
theorem actual_current_double_finite_character_residual (h:ℝ) (nonnegative:0≤h)
 (bounded:h≤Real.log 2) (n:Nat):
 OriginalKCompleteMCofinalSource.actualFiniteSourceCharacter observation nontrivial half h nonnegative bounded n-
 actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded n=
 actualFourierDualCharacterResidual observation nontrivial half h n :=by
 have price:=actual_complete_M_Fourier_dual_finite_residual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n
 have generated:CurrentM.actualFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n=
  actualDoubleFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n+
  CurrentM.actualMSourceWeight (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)*
  actualFiniteFourierDualPriceRead (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n*
  actualFourierDualSourceResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) n :=by
  linear_combination price
 unfold OriginalKCompleteMCofinalSource.actualFiniteSourceCharacter
 rw [generated]
 unfold actualDoubleFiniteSourceCharacter OriginalKCompleteMCofinalSource.actualCharacterSourceRead actualFourierDualCharacterResidual
 dsimp only
 unfold CurrentM.actualMSourceWeight
 simp only [star_mul,star_add,star_sub]
 ring

/-- The new literal Gram residue tends to zero from both actual whole source closures. -/
theorem actual_Fourier_dual_source_residual_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualFourierDualSourceResidual c) atTop (𝓝 0) :=by
 have constant:Tendsto (fun _:Nat=>OriginalKStaticKernelSourceGramSource.actualFourierDualGram c) atTop
  (𝓝 (OriginalKStaticKernelSourceGramSource.actualFourierDualGram c)):=tendsto_const_nhds
 have generated:=constant.sub (actual_original_Fourier_dual_source_tendsto c)
 simpa only [actual_original_Fourier_dual_source_residual,sub_self] using generated

/-- The source-current finite Tate read and actual two-leg Gram closure pay the character's own new residue. -/
theorem actual_Fourier_dual_character_residual_tendsto (h:ℝ):
 Tendsto (actualFourierDualCharacterResidual observation nontrivial half h) atTop (𝓝 0) :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let w:=CurrentM.actualMSourceWeight c
 have constant (value:ℂ):Tendsto (fun _:Nat=>value) atTop (𝓝 value):=tendsto_const_nhds
 have read:=((CurrentM.actual_complete_M_cofinal_source c h).add
  (constant (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*
   OriginalKCompleteMResidualSource.actualMSourceVCoefficient c h))).const_mul (-2:ℂ)
 have cost:=((read.const_mul w).mul (actual_Fourier_dual_source_residual_tendsto c))
 have zero:Tendsto (fun n=>w*actualFiniteFourierDualPriceRead c h n*actualFourierDualSourceResidual c n) atTop (𝓝 0):=by
  simpa only [actualFiniteFourierDualPriceRead,mul_zero] using cost
 have source:=(zero.star.const_mul (χ*A*star a*w)).sub (zero.const_mul (star χ*A*a*star w))
 unfold actualFourierDualCharacterResidual
 simpa only [mul_zero,sub_zero,star_zero] using source

/-- Exact original character value readout; no source constructor consumes this value. -/
def actualOriginalCharacterValue (h:ℝ):ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 (star κ*κ)*(star D*D)*(OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
  OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)

/-- The independent original character consumes both actual source programmes and their faithful residues. -/
theorem actual_double_source_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded) atTop
  (𝓝 (actualOriginalCharacterValue observation nontrivial half h)) :=by
 have prior:=OriginalKCompleteMCofinalSource.actual_complete_source_character_tendsto observation nontrivial half h nonnegative bounded
 have paid:=prior.sub (actual_Fourier_dual_character_residual_tendsto observation nontrivial half h)
 have actual: (fun n=>OriginalKCompleteMCofinalSource.actualFiniteSourceCharacter observation nontrivial half h nonnegative bounded n-
  actualFourierDualCharacterResidual observation nontrivial half h n)=
  actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded :=by
  funext n
  have source:=actual_current_double_finite_character_residual observation nontrivial half h nonnegative bounded n
  linear_combination source
 rw [actual] at paid
 simpa only [sub_zero,actualOriginalCharacterValue] using paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
