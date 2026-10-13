import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSingleReturnEulerRAction.Inverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem actual_R_add (z : ℂ) (right : 1/4<z.re) (left rightField : BurnolL2) :
 burnolDirectRightResolvent z (left+rightField)=
 burnolDirectRightResolvent z left+burnolDirectRightResolvent z rightField :=by
 have source:=burnolDirectRightResolvent_sub z right left (-rightField)
 rw [←neg_one_smul ℂ rightField,burnolDirectRightResolvent_smul] at source
 simpa only [neg_one_smul,sub_neg_eq_add] using source

/-- Repeated original R directly generates all Jordan forcing columns with their original units. -/
theorem actual_return_forcing_J_inventory (coordinate : BurnolCompletedMellinCoordinate) :
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 OriginalKFourierKernelDependentRAction.actualResonantField z (actualReturnForcing coordinate)=
 ((1/2:ℂ)*OriginalRieszSource.Kernel.A coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeV-
 ((1/2:ℂ)*OriginalRieszSource.Kernel.beta coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeU+
 ((1/2:ℂ)*(star coordinate.value-1)*actualReturnEndpoint coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z Native.seed :=by
 dsimp only
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).rightHalf]
 simp_rw [←OriginalKFourierKernelDependentRAction.actual_resonant_repeated_R
  ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) right]
 unfold actualReturnForcing
 simp_rw [burnolDirectRightResolvent_smul,actual_R_add
  ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) right,
  burnolDirectRightResolvent_sub ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) right]
 simp_rw [burnolDirectRightResolvent_smul]
 module

/-- The source-generated endpoint difference is the original native kernel coefficient and A, not an input identification. -/
theorem actual_return_endpoint_native_relation (coordinate : BurnolCompletedMellinCoordinate) :
 actualReturnEndpoint coordinate-OriginalKFourierKernelDependentRAction.actualNativeKernelCoefficient coordinate=
 OriginalRieszSource.Kernel.A coordinate :=by
 unfold actualReturnEndpoint OriginalKFourierKernelDependentRAction.actualNativeKernelCoefficient OriginalRieszSource.Kernel.A
 ring

/-- Original ambient native kernel and actual return combine to one actual A/beta Jordan source inventory. -/
theorem actual_complete_FK_R_source_inventory (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 burnolDirectRightResolvent z (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))+
 burnolDirectRightResolvent z (Native.actualWholeSingleReturn coordinate)=
 ((1/2:ℂ)*OriginalRieszSource.Kernel.A coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeV-
 ((1/2:ℂ)*OriginalRieszSource.Kernel.beta coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z OriginalRieszSource.Response.wholeU+
 ((1/2:ℂ)*(star coordinate.value-1)*OriginalRieszSource.Kernel.A coordinate) •
  OriginalKFourierKernelDependentRAction.actualResonantField z Native.seed+
 OriginalRieszSource.Kernel.A coordinate • OriginalKConstantSeedWholeRAction.actualWholeSeedRField dual :=by
 dsimp only
 rw [OriginalKFourierKernelDependentRAction.actual_native_kernel_resonant_R,actual_return_R_response,
  actual_return_forcing_J_inventory]
 unfold OriginalKFourierKernelDependentRAction.actualResonantNativeKernelField
 have source:=actual_return_endpoint_native_relation coordinate
 have seedCoefficient:=congrArg (fun factor:ℂ=>((1/2:ℂ)*(star coordinate.value-1)*factor) •
  OriginalKFourierKernelDependentRAction.actualResonantField
    ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) Native.seed) source
 have fieldCoefficient:=congrArg (fun factor:ℂ=>factor • OriginalKConstantSeedWholeRAction.actualWholeSeedRField
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)) source
 dsimp only [OriginalKQuarterTailPhysicalSource.actualStarSource]
 dsimp only [OriginalKQuarterTailPhysicalSource.actualStarSource] at seedCoefficient fieldCoefficient
 linear_combination (norm:=module) seedCoefficient+fieldCoefficient

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
