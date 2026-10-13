import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitivePhysicalSourceAction.Effect
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
local instance primitivePhysicalPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "P" => burnolEvenAmbientProjection
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

/-- The original physical own reader consumes the primitive's same dependent P face. -/
theorem actual_primitive_own_physical_read (h:ℝ) (physical:BurnolPaAmbientCarrier):
 inner ℂ physical (P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h))=
 inner ℂ (physical:BurnolL2) (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h):=
 (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
  physical (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)

def actualFinitePrimitivePairPrice (h:ℝ) (n:Nat):ℂ:=
 star (inner ℂ (K c+Fphysical (K c)) (actualFinitePrimitiveActionField observation nontrivial half h n))
def actualFinitePrimitiveSiblingPrice (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (K c-Fphysical (K c)) (actualFinitePrimitiveActionField observation nontrivial half h n)
def actualPrimitivePairPriceResidual (h:ℝ) (n:Nat):ℂ:=
 star (inner ℂ (K c+Fphysical (K c)) (actualPrimitiveActionResidual observation nontrivial half h n))
def actualPrimitiveSiblingPriceResidual (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (K c-Fphysical (K c)) (actualPrimitiveActionResidual observation nontrivial half h n)

/-- Both original own feet consume the generated whole primitive action, preserving the actual scalar-star directions of the existing kappa. -/
theorem actual_original_primitive_two_price_residuals (h:ℝ) (n:Nat):
 star (Physical.actualResponseKappa c)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
  (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
 actualFinitePrimitivePairPrice observation nontrivial half h n=actualPrimitivePairPriceResidual observation nontrivial half h n ∧
 Physical.actualResponseKappa c*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
  (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
 actualFinitePrimitiveSiblingPrice observation nontrivial half h n=actualPrimitiveSiblingPriceResidual observation nontrivial half h n :=by
 have source:=actual_original_primitive_finite_source_residual observation nontrivial half h n
 have first:=congrArg (fun value:BurnolPaAmbientCarrier=>star (inner ℂ (K c+Fphysical (K c)) value)) source
 have second:=congrArg (inner ℂ (K c-Fphysical (K c))) source
 rw [inner_sub_right,inner_smul_right,star_sub,star_mul] at first
 rw [inner_sub_right,inner_smul_right] at second
 rw [OriginalKPairedResponseGramAction.original_kernel_paired_qualification,
  OriginalKPairedResponseGramAction.original_kernel_sibling_qualification]
 unfold actualFinitePrimitivePairPrice actualFinitePrimitiveSiblingPrice
  actualPrimitivePairPriceResidual actualPrimitiveSiblingPriceResidual
 rw [actual_primitive_own_physical_read] at first second
 have physicalFourier:(Fphysical (K c):BurnolL2)=fourierL2 (K c:BurnolL2):=rfl
 rw [←physicalFourier]
 constructor
 · simpa only [Submodule.coe_add,inner_add_left,mul_comm] using first
 · simpa only [Submodule.coe_sub,inner_sub_left] using second

/-- Each actual own-foot error is paid from the full composed original source action error, never from a positive projected margin. -/
theorem actual_original_primitive_two_price_errors (h:ℝ) (n:Nat):
 ‖actualPrimitivePairPriceResidual observation nontrivial half h n‖≤
 ‖K c+Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n ∧
 ‖actualPrimitiveSiblingPriceResidual observation nontrivial half h n‖≤
 ‖K c-Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n :=by
 have source:=actual_original_primitive_finite_source_error observation nontrivial half h n
 rw [actual_original_primitive_finite_source_residual] at source
 constructor
 · unfold actualPrimitivePairPriceResidual
   rw [norm_star]
   exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))
 · unfold actualPrimitiveSiblingPriceResidual
   exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))

theorem actual_primitive_two_price_residuals_tendsto (h:ℝ):
 Tendsto (actualPrimitivePairPriceResidual observation nontrivial half h) atTop (𝓝 0) ∧
 Tendsto (actualPrimitiveSiblingPriceResidual observation nontrivial half h) atTop (𝓝 0) :=by
 have error:=actual_primitive_action_error_tendsto observation nontrivial half h
 have source:=actual_original_primitive_two_price_errors observation nontrivial half h
 constructor
 · apply tendsto_zero_iff_norm_tendsto_zero.mpr
   exact squeeze_zero (fun n=>norm_nonneg _) (fun n=>(source n).1)
    (by simpa only [mul_zero] using error.const_mul ‖K c+Fphysical (K c)‖)
 · apply tendsto_zero_iff_norm_tendsto_zero.mpr
   exact squeeze_zero (fun n=>norm_nonneg _) (fun n=>(source n).2)
    (by simpa only [mul_zero] using error.const_mul ‖K c-Fphysical (K c)‖)

/-- The same complete original K forcing source field is also consumed by its own K reader; this is grouped with the primitive action, not a new source engine. -/
def actualFiniteKForcingPrice (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n)
  (OriginalKFourierForcingCofinalAction.actualFiniteForcingField c h n)

def actualKForcingPriceResidual (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (OriginalKFullKernelCofinalSource.actualWholeKernelSourceResidual c n)
  (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))+
 inner ℂ (OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n)
  (OriginalKFourierForcingCofinalAction.actualForcingFieldResidual c h n)

/-- The paid same whole forcing action and original K energy Ward remove the remaining free K forcing price in the complete consumer. -/
theorem actual_original_K_Ward_finite_residual (h:ℝ) (n:Nat):
 OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
 actualFiniteKForcingPrice observation nontrivial half h n=actualKForcingPriceResidual observation nontrivial half h n :=by
 have first:=OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_residual c n
 have second:=OriginalKFourierForcingCofinalAction.actual_original_forcing_field_residual c h n
 have generated:inner ℂ (K c:BurnolL2)
  (OriginalKSourceScaledMaximalResponse.originalForcingPair observation nontrivial half h)-
  actualFiniteKForcingPrice observation nontrivial half h n=actualKForcingPriceResidual observation nontrivial half h n:=by
  unfold actualKForcingPriceResidual
  rw [←first,←second,inner_sub_left,inner_sub_right]
  unfold actualFiniteKForcingPrice OriginalKSourceScaledMaximalResponse.originalForcingPair
  ring
 rw [OriginalKSourceScaledMaximalResponse.actual_original_K_energy_ward] at generated
 exact generated

/-- The already-generated full forcing field pays its original own K foot with the same exact two-source costs. -/
theorem actual_K_forcing_price_residual_error (h:ℝ) (n:Nat):
 ‖actualKForcingPriceResidual observation nontrivial half h n‖≤
 OriginalKFourierForcingCofinalAction.actualFourierForcingPriceError c h n :=by
 unfold actualKForcingPriceResidual OriginalKFourierForcingCofinalAction.actualFourierForcingPriceError
 have first:=OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_error c n
 rw [OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_residual] at first
 have second:=OriginalKFourierForcingCofinalAction.actual_original_forcing_field_error c h n
 rw [OriginalKFourierForcingCofinalAction.actual_original_forcing_field_residual] at second
 calc
  _≤‖inner ℂ (OriginalKFullKernelCofinalSource.actualWholeKernelSourceResidual c n)
    (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))‖+
    ‖inner ℂ (OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n)
     (OriginalKFourierForcingCofinalAction.actualForcingFieldResidual c h n)‖:=norm_add_le _ _
  _≤‖OriginalKFullKernelCofinalSource.actualWholeKernelSourceResidual c n‖*
    ‖OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)‖+
    ‖OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n‖*
     ‖OriginalKFourierForcingCofinalAction.actualForcingFieldResidual c h n‖:=
   add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
  _≤_:=add_le_add (mul_le_mul_of_nonneg_right first (norm_nonneg _))
   (mul_le_mul (OriginalKFullKernelCofinalSource.actual_finite_whole_kernel_source_norm c n) second
    (norm_nonneg _) (by unfold OriginalKFullKernelCofinalSource.actualWholeKernelSourceError;positivity))

theorem actual_K_forcing_price_residual_tendsto (h:ℝ):
 Tendsto (actualKForcingPriceResidual observation nontrivial half h) atTop (𝓝 0) :=by
 have first:=OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_tendsto c
 have second:=OriginalKFourierForcingCofinalAction.actual_original_forcing_field_tendsto c h
 have prices:=first.inner (𝕜:=ℂ) second
 have target:=OriginalKSourceScaledMaximalResponse.actual_original_K_energy_ward observation nontrivial half h
 have source:Tendsto (actualFiniteKForcingPrice observation nontrivial half h) atTop
  (𝓝 (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h)):=by
  change Tendsto _ atTop (𝓝 (inner ℂ (K c:BurnolL2)
   (OriginalKSourceScaledMaximalResponse.originalForcingPair observation nontrivial half h))) at prices
  rw [target] at prices
  exact prices
 have constant:Tendsto (fun _:Nat=>OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h) atTop
  (𝓝 (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h)):=tendsto_const_nhds
 simpa only [actual_original_K_Ward_finite_residual,sub_self] using constant.sub source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
