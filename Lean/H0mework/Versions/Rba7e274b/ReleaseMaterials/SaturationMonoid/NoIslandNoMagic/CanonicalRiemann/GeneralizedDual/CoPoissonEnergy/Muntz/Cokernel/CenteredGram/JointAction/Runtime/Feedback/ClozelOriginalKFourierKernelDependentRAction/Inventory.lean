import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Native
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
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








/-- The whole Jordan/source response is physically read only after its original edge and quarter-seed stocks are generated. -/
theorem actual_resonant_native_field_price (coordinate : BurnolCompletedMellinCoordinate)
 (physical : BurnolPaAmbientCarrier) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 inner ℂ (actualResonantNativeKernelField coordinate) (fourierL2 (physical : BurnolL2))=
 star (actualNativeKernelCoefficient coordinate)*
 (-(coordinate.value-1)/2*inner ℂ (actualResonantField (dual.value/2) Whole.seed)
    (fourierL2 (physical : BurnolL2))+
  (2/(coordinate.value-1):ℂ)*
   (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
     inner ℂ (burnolCompletedMellinRieszVector coordinate)
       (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)+
    (1/2:ℂ)*Paid.actualMean (fourierL2 (physical : BurnolL2)))) :=by
 dsimp only
 unfold actualResonantNativeKernelField Whole.actualWholeSeedRField
 dsimp only
 have dualtwice : OriginalKQuarterTailPhysicalSource.actualStarSource
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)=coordinate :=by
  cases coordinate
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 rw [dualtwice,inner_smul_left,inner_sub_left,inner_smul_left,inner_smul_left,inner_add_left]
 have input:=OriginalKConstantSeedWholeRAction.actual_edge_physical_input_price coordinate
   (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)
 have seed:=OriginalKConstantContactSourceAction.actual_constant_seed_input_price
   (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)
 change inner ℂ (OriginalRieszFiniteSource.edgePrimitive coordinate) (fourierL2 (physical : BurnolL2))=_ at input
 change inner ℂ Whole.seed (fourierL2 (physical : BurnolL2))=
   (1/2:ℂ)*Paid.actualMean (fourierL2 (physical : BurnolL2)) at seed
 rw [input,seed]
 simp only [OriginalKQuarterTailPhysicalSource.actualStarSource,starRingEnd_apply,
   star_div₀,star_neg,star_sub,star_one,star_ofNat,star_star]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
