import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Coefficient
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
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

local notation "M" => BurnolQuarterMeanZeroCarrier
local instance cofinalPricePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem actual_whole_mean_zero (value : M) : Paid.actualMean (actualWholeRead value)=0 :=by
 unfold actualWholeRead Paid.actualMean
 change ((‖intervalConstant q‖^2:ℂ)⁻¹)*inner ℂ (intervalConstant q)
  (burnolRadiusRestriction q (burnolRadiusZeroExtension q (value : BurnolQuarterIntervalL2)))=0
 rw [burnolRadiusRestriction_zeroExtension]
 have source:inner ℂ (intervalConstant q) (value : BurnolQuarterIntervalL2)=0:=
  (Submodule.mem_orthogonal _ _).mp value.property _ (Submodule.mem_span_singleton_self _)
 rw [source,mul_zero]

def actualFirstPriceWeight (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let rate:=dual.value/2-1/2
 let point:=(((2*q:ℝ):ℂ)*(q:ℂ)^(-dual.value))
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 (-1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star (point/rate/rate)+
 OriginalKCompactJordanRankSource.actualNativeTailRPrice observation nontrivial half h shift

def actualSecondPriceWeight (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let rate:=dual.value/2-1/2
 let point:=(((2*q:ℝ):ℂ)*(q:ℂ)^(-dual.value))
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)*star (point/rate)+
 (-(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
  (2:ℂ)*burnolMellinGapMoment coordinate.value*Paid.actualMean (Fphysical : BurnolL2))

def actualJordanPriceRead (h shift : ℝ) : M→L[ℝ]ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 actualFirstPriceWeight observation nontrivial half h shift •
  Complex.conjCLE.toContinuousLinearMap.comp ((actualFirstRead coordinate).restrictScalars ℝ)+
 actualSecondPriceWeight observation nontrivial half h •
  Complex.conjCLE.toContinuousLinearMap.comp ((actualSecondRead coordinate).restrictScalars ℝ)

/-- Actual mean-zero source coefficients are consumed in the original physical price with every original price weight retained. -/
theorem actual_price_reader_source (value : M) (h shift : ℝ) :
 actualJordanPriceRead observation nontrivial half h shift value=
 OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half
  (actualWholeRead value) h shift :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let rate:=dual.value/2-1/2
 unfold actualJordanPriceRead
 change actualFirstPriceWeight observation nontrivial half h shift*star (actualFirstRead coordinate value)+
  actualSecondPriceWeight observation nontrivial half h*star (actualSecondRead coordinate value)=_
 rw [actual_first_read_source,actual_second_read_source]
 unfold actualFirstPriceWeight actualSecondPriceWeight
 unfold OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice
 unfold OriginalKCompactJordanRankSource.actualSecondMean OriginalKCompactJordanRankSource.actualFirstMean
 dsimp only
 rw [actual_whole_mean_zero value]
 dsimp only [coordinate,dual,rate]
 simp only [star_sub,star_div₀,star_mul,star_zero,star_ofNat,star_one]
 push_cast
 simp only [div_eq_mul_inv]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
