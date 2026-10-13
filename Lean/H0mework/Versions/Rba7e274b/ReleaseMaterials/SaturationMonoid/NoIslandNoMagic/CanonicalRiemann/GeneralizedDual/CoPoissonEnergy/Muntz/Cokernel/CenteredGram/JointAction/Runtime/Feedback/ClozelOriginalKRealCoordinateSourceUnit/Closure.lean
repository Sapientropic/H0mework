import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance unweightedClosureComplete : CompleteSpace BurnolPaAmbientCarrier :=by
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




/-- The fully restored original whole R M inventory keeps the original source control and every residual component. -/
theorem actual_original_unweighted_M_inventory_error (h:ℝ) (n:Nat):
 ‖burnolEvenAmbientProjection (burnolDirectRightResolvent ((c).value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))-
 OriginalKCompleteMCofinalSource.actualFiniteMInventoryField c h n‖≤
 ‖OriginalKCompleteMResidualSource.actualMeanZeroCompactRField c‖*‖OriginalKCompleteMCofinalSource.actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 rw [actual_original_unweighted_M_source_action]
 exact OriginalKCompleteMCofinalSource.actual_complete_M_inventory_error c h n

/-- The same target is read after its original source weight, without target input to any producer. -/
theorem actual_original_character_source_weight_factor (h:ℝ):
 OriginalKCharacterActionSource.actualDeterminantFreeOriginalCharacter observation nontrivial half h=
 actualOriginalCharacterSourceWeight observation nontrivial half*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h :=by
 unfold OriginalKCharacterActionSource.actualDeterminantFreeOriginalCharacter actualOriginalCharacterSourceWeight
 ring

/-- The independent original kernel cross consumes the actual real-coordinate source units and the complete source closures, with no determinant or response prefactor left. -/
theorem actual_original_unweighted_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded) atTop
 (𝓝 (OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)) :=by
 let W:=actualOriginalCharacterSourceWeight observation nontrivial half
 have unit:W≠0:=actual_original_character_source_weight_ne_zero observation nontrivial half
 have prior:=OriginalKCharacterActionSource.actual_determinant_free_character_tendsto observation nontrivial half h nonnegative bounded
 have generated:=prior.const_mul W⁻¹
 have source:(fun n=>W⁻¹*OriginalKCharacterActionSource.actualDeterminantFreeFiniteCharacter observation nontrivial half h nonnegative bounded n)=
  actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded:=by
  funext n
  rw [actual_current_unweighted_character_factor]
  change W⁻¹*(W*actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded n)=_
  rw [←mul_assoc,inv_mul_cancel₀ unit,one_mul]
 have target:W⁻¹*OriginalKCharacterActionSource.actualDeterminantFreeOriginalCharacter observation nontrivial half h=
  OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h:=by
  rw [actual_original_character_source_weight_factor]
  change W⁻¹*(W*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)=_
  rw [←mul_assoc,inv_mul_cancel₀ unit,one_mul]
 rw [source,target] at generated
 exact generated

/-- Every faithful source residue closes after the same generated units; no residual is assumed erased. -/
theorem actual_unweighted_character_residual_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 Tendsto (actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded) atTop (𝓝 0) :=by
 unfold actualUnweightedCharacterResidual
 simpa only [mul_zero] using (OriginalKCharacterActionSource.actual_determinant_free_character_residual_tendsto
  observation nontrivial half h nonnegative bounded).const_mul (actualOriginalCharacterSourceWeight observation nontrivial half)⁻¹

/-- Inverse source fees are retained explicitly; this norm is never a projected positive margin. -/
theorem actual_unweighted_character_residual_source_cost (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 ‖actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n‖=
 ‖(actualOriginalCharacterSourceWeight observation nontrivial half)⁻¹‖*
 ‖OriginalKCharacterActionSource.actualDeterminantFreeCharacterResidual observation nontrivial half h nonnegative bounded n‖ :=by
 unfold actualUnweightedCharacterResidual
 exact norm_mul _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
