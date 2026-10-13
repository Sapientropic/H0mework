import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactJordanRankSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
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

local instance compactJordanNativeComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualNativeTailRPrice (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 let foot:=star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
  inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
  (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)
 (-2:ℂ)*star (OriginalKFourierKernelDependentRAction.actualNativeKernelCoefficient coordinate)*
  (-(coordinate.value-1)/2*
   (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
    OriginalKJordanExteriorSourceAction.actualExteriorSourcePrice observation nontrivial half h shift)+
   (2/(coordinate.value-1):ℂ)*foot)-
 ((8:ℂ)*burnolMellinGapMoment coordinate.value/(coordinate.value-1))*foot

/-- The native response actually consumes the original full exterior finite field and all beyond-band fees. -/
theorem actual_native_tail_R_price (h shift : ℝ) (nonnegative : 0≤shift) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 actualTailRPrice coordinate material=actualNativeTailRPrice observation nontrivial half h shift :=by
 have price:=OriginalKJordanExteriorSourceAction.actual_native_exterior_source_price observation nontrivial half h shift nonnegative
 dsimp only at price
 unfold actualTailRPrice actualNativeTailRPrice
 dsimp only
 rw [price]

def actualNativeCompactJordanPrice (source : BurnolL2) (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star (actualSecondMean coordinate source)+
 star (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual (actualFirstCut coordinate source))*
  (-(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (2:ℂ)*burnolMellinGapMoment coordinate.value*Paid.actualMean (Fphysical : BurnolL2))+
 star (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source)*
  actualNativeTailRPrice observation nontrivial half h shift

def actualCompactJordanFKMeanPrice (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A/2)*actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeV h shift-
 (b/2)*actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeU h shift+
 ((coordinate.value-1)*A/2)*
  (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
   OriginalKJordanExteriorSourceAction.actualExteriorSourcePrice observation nontrivial half h shift)-
 (2*A/(coordinate.value-1))*
  (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
    inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2))

/-- Same actual original U/V source qualifications and generated second R prices are consumed in original FK. -/
theorem actual_original_UV_Jordan_price_consumer (h shift : ℝ) (nonnegative : 0≤shift) :
 OriginalKSingleReturnEulerRAction.actualReturnJointFKMeanPrice observation nontrivial half h shift=
 actualCompactJordanFKMeanPrice observation nontrivial half h shift :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 have qualified:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 have u:=actual_compact_Jordan_physical_price coordinate OriginalRieszSource.Response.wholeU
  qualified.1 qualified.2.1 material
 have v:=actual_compact_Jordan_physical_price coordinate OriginalRieszSource.Response.wholeV
  qualified.2.2.1 qualified.2.2.2 material
 dsimp only at u v
 change inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField
  ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) OriginalRieszSource.Response.wholeU)
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius material : BurnolL2)=_ at u
 change inner ℂ (OriginalKFourierKernelDependentRAction.actualResonantField
  ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) OriginalRieszSource.Response.wholeV)
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius material : BurnolL2)=_ at v
 dsimp only [coordinate,material] at u v
 unfold OriginalKSingleReturnEulerRAction.actualReturnJointFKMeanPrice actualCompactJordanFKMeanPrice
 dsimp only
 rw [u,v]
 unfold actualCompactJordanPrice actualNativeCompactJordanPrice
 dsimp only
 rw [actual_native_tail_R_price observation nontrivial half h shift nonnegative]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
