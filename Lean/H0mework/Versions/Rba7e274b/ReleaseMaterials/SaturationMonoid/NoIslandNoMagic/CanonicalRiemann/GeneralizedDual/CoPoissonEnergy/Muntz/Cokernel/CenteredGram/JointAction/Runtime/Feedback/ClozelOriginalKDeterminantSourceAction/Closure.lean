import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDeterminantSourceAction.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance determinantClosureComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "K" => burnolCompletedMellinRieszVector
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "H" => OriginalKCommonGapKernelSource.actualCommonField
local notation "velocity" => OriginalKCommonGapKernelSource.actualCommonVelocity

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)



/-- Whole R M finite material has the original same-source bound after the determinant gate has been discharged. -/
theorem actual_original_M_determinant_free_inventory_error (h:ℝ) (n:Nat):
 ‖OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
  burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))-
  OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c • OriginalKCompleteMCofinalSource.actualFiniteMInventoryField c h n‖≤
 ‖OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c‖*
 ‖OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c‖*‖OriginalKCompleteMCofinalSource.actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 rw [actual_original_M_determinant_free_action,←smul_sub,norm_smul]
 exact (mul_le_mul_of_nonneg_left (OriginalKCompleteMCofinalSource.actual_complete_M_inventory_error c h n)
  (norm_nonneg _)).trans_eq (by ring)

/-- The original current character target reads its literal determinant factor; this readout is never a source argument. -/
theorem actual_original_character_determinant_factor (h:ℝ):
 OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
 (star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
 actualDeterminantFreeOriginalCharacter observation nontrivial half h :=by
 unfold OriginalKFullKernelCofinalSource.actualOriginalCharacterValue actualDeterminantFreeOriginalCharacter
 dsimp only
 ring

/-- The independent consumer uses the generated unit to remove D from the current complete character, preserving kappa and every source programme. -/
theorem actual_determinant_free_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded) atTop
 (𝓝 (actualDeterminantFreeOriginalCharacter observation nontrivial half h)) :=by
 let W:=star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c
 have unit:W≠0:=mul_ne_zero (star_ne_zero.mpr (actual_original_common_determinant_ne_zero observation nontrivial half))
  (actual_original_common_determinant_ne_zero observation nontrivial half)
 have prior:=OriginalKPaCountingSourceAction.actual_finite_Pa_counting_character_tendsto observation nontrivial half h nonnegative bounded
 have generated:=prior.const_mul W⁻¹
 have actual:(fun n=>W⁻¹*OriginalKPaCountingSourceAction.actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded n)=
  actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded:=by
  funext n
  have source:=actual_current_finite_character_determinant_factor observation nontrivial half h nonnegative bounded n
  change OriginalKPaCountingSourceAction.actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded n=
   W*actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n at source
  rw [source,←mul_assoc,inv_mul_cancel₀ unit,one_mul]
 have target:W⁻¹*OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
  actualDeterminantFreeOriginalCharacter observation nontrivial half h:=by
  have source:=actual_original_character_determinant_factor observation nontrivial half h
  change OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
   W*actualDeterminantFreeOriginalCharacter observation nontrivial half h at source
  rw [source,←mul_assoc,inv_mul_cancel₀ unit,one_mul]
 rw [actual,target] at generated
 exact generated

/-- The five original source residues close through their actual complete character equation after the source determinant has been generated. -/
theorem actual_determinant_free_character_residual_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualDeterminantFreeCharacterResidual observation nontrivial half h nonnegative bounded) atTop (𝓝 0) :=by
 have actual:=actual_determinant_free_character_tendsto observation nontrivial half h nonnegative bounded
 have generated:=(tendsto_const_nhds (x:=actualDeterminantFreeOriginalCharacter observation nontrivial half h)).sub actual
 simp only [sub_self] at generated
 have field:(fun n=>actualDeterminantFreeOriginalCharacter observation nontrivial half h-
  actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n)=
  actualDeterminantFreeCharacterResidual observation nontrivial half h nonnegative bounded:=by
  funext n
  have source:=actual_original_determinant_free_character observation nontrivial half h nonnegative bounded n
  linear_combination source
 rw [field] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
