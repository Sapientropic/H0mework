import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitivePhysicalSourceAction.Source
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
local instance primitivePhysicalEffectComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKPairedResponseGramAction.originalOutside
local notation "R" => burnolDirectRightResolventCLM

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

/-- The whole raw outside primitive is generated from its actual original R action; no physical-dilation exchange removes it. -/
theorem actual_original_primitive_outside_source:
 actualPrimitiveOutsideSource observation nontrivial half=
 Return.sourceA observation • O (R c (K c:BurnolL2)) :=by
 have source:=Return.original_return_source_equation observation nontrivial half
 have generated:=congrArg O source
 rw [map_sub,map_smul,OriginalKCombCofinalRAction.original_R_direct] at generated
 have physical:O (K c:BurnolL2)=0:=by
  unfold OriginalKPairedResponseGramAction.originalOutside
  exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (by
   simpa only [Submodule.orthogonal_orthogonal] using (K c).property)
 change Return.sourceA observation • O (R c (K c:BurnolL2))-O (K c:BurnolL2)=
  actualPrimitiveOutsideSource observation nontrivial half at generated
 rw [physical,sub_zero] at generated
 exact generated.symm

def actualPrimitiveOutsideAction (h:ℝ):BurnolL2→L[ℂ]BurnolPaAmbientCarrier:=
 (Physical.actualResponseKappa c*Return.sourceA observation) •
  ((burnolEvenAmbientProjection).comp
   ((OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h).comp (OriginalKPairedResponseGramAction.originalOutside.comp (R c))))

def actualFinitePrimitiveActionField (h:ℝ) (n:Nat):BurnolPaAmbientCarrier:=
 P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
  (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))+
 actualPrimitiveOutsideAction observation nontrivial half h
  (OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n)

def actualPrimitiveActionResidual (h:ℝ) (n:Nat):BurnolPaAmbientCarrier:=
 actualPrimitiveOutsideAction observation nontrivial half h
  (OriginalKFullKernelCofinalSource.actualWholeKernelSourceResidual c n)

/-- The same full primitive finite inventory consumes the actual outside R source programme before either original own foot is read. -/
theorem actual_original_primitive_finite_source_residual (h:ℝ) (n:Nat):
 Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
 actualFinitePrimitiveActionField observation nontrivial half h n=
 actualPrimitiveActionResidual observation nontrivial half h n :=by
 have original:=actual_original_weighted_primitive_finite_source observation nontrivial half h
 dsimp only at original
 rw [original]
 unfold actualWeightedPrimitiveFiniteSource
 rw [actual_original_primitive_outside_source,map_smul,map_smul,smul_smul]
 change _=actualPrimitiveActionResidual observation nontrivial half h n
 unfold actualFinitePrimitiveActionField actualPrimitiveActionResidual
 have source:=congrArg (actualPrimitiveOutsideAction observation nontrivial half h)
  (OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_residual c n)
 rw [map_sub] at source
 change P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
  (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))+
  actualPrimitiveOutsideAction observation nontrivial half h (K c:BurnolL2)-
  (P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
   (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))+
   actualPrimitiveOutsideAction observation nontrivial half h (OriginalKFullKernelCofinalSource.actualFiniteWholeKernelSource c n))=_
 linear_combination (norm:=module) source

def actualPrimitiveActionError (h:ℝ) (n:Nat):ℝ:=
 ‖actualPrimitiveOutsideAction observation nontrivial half h‖*
  OriginalKFullKernelCofinalSource.actualWholeKernelSourceError c n

/-- The actual composed R/outside/finite-action/dependent-P source pays its own whole primitive action error; no norm is granted to Pa. -/
theorem actual_original_primitive_finite_source_error (h:ℝ) (n:Nat):
 ‖Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
  actualFinitePrimitiveActionField observation nontrivial half h n‖≤
 actualPrimitiveActionError observation nontrivial half h n :=by
 rw [actual_original_primitive_finite_source_residual]
 unfold actualPrimitiveActionResidual actualPrimitiveActionError
 have source:=OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_error c n
 rw [OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_residual] at source
 exact ((actualPrimitiveOutsideAction observation nontrivial half h).le_opNorm _).trans
  (mul_le_mul_of_nonneg_left source (norm_nonneg _))

theorem actual_primitive_action_error_tendsto (h:ℝ):
 Tendsto (actualPrimitiveActionError observation nontrivial half h) atTop (𝓝 0) :=by
 unfold actualPrimitiveActionError
 simpa only [mul_zero] using (OriginalKFullKernelCofinalSource.actual_whole_kernel_error_tendsto c).const_mul
  ‖actualPrimitiveOutsideAction observation nontrivial half h‖

/-- The primitive action is consumed as the closure of the same original ambient source R programme, with its existing kappa retained. -/
theorem actual_original_primitive_finite_source_tendsto (h:ℝ):
 Tendsto (actualFinitePrimitiveActionField observation nontrivial half h) atTop
  (𝓝 (Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h))) :=by
 have constant:Tendsto (fun _:Nat=>P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
  (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))) atTop
  (𝓝 (P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
   (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2)))):=tendsto_const_nhds
 have generated:=constant.add
  (((actualPrimitiveOutsideAction observation nontrivial half h).continuous.tendsto _).comp
   (OriginalKFullKernelCofinalSource.actual_original_whole_kernel_source_tendsto c))
 have target:=actual_original_weighted_primitive_finite_source observation nontrivial half h
 dsimp only at target
 unfold actualWeightedPrimitiveFiniteSource at target
 rw [actual_original_primitive_outside_source,map_smul,map_smul,smul_smul] at target
 change Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
  P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
    (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))+
  actualPrimitiveOutsideAction observation nontrivial half h (K c:BurnolL2) at target
 rw [←target] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
