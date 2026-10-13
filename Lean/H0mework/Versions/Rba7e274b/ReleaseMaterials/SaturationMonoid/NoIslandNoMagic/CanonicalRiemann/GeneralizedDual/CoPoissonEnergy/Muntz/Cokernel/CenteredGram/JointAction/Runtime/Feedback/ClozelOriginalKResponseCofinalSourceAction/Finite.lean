import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Price
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

def actualRetainedFKStock (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 ((coordinate.value-1)*A/2)*
  (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
   OriginalKJordanExteriorSourceAction.actualExteriorSourcePrice observation nontrivial half h shift)-
 (2*A/(coordinate.value-1))*
  (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
    inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
   (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2))

def actualFiniteFKPrice (n : Nat) (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A/2)*actualJordanPriceRead observation nontrivial half h shift (actualV n)-
 (b/2)*actualJordanPriceRead observation nontrivial half h shift (actualU n)+
 actualRetainedFKStock observation nontrivial half h shift

def actualFKResidual (n : Nat) (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 (star (OriginalRieszSource.Kernel.A coordinate)/2)*
  actualJordanPriceRead observation nontrivial half h shift (OriginalRieszSource.Response.v-actualV n)-
 (star (OriginalRieszSource.Kernel.beta coordinate)/2)*
  actualJordanPriceRead observation nontrivial half h shift (OriginalRieszSource.Response.u-actualU n)

/-- The actual finite source pays the original FK price with its complete source-generated residual. -/
theorem actual_original_FK_finite_price (n : Nat) (h shift : ℝ) :
 OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice observation nontrivial half h shift=
 actualFiniteFKPrice observation nontrivial half n h shift+actualFKResidual observation nontrivial half n h shift :=by
 have u:=actual_price_reader_source observation nontrivial half OriginalRieszSource.Response.u h shift
 have v:=actual_price_reader_source observation nontrivial half OriginalRieszSource.Response.v h shift
 change actualJordanPriceRead observation nontrivial half h shift OriginalRieszSource.Response.u=
  OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeU h shift at u
 change actualJordanPriceRead observation nontrivial half h shift OriginalRieszSource.Response.v=
  OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeV h shift at v
 unfold actualFiniteFKPrice actualFKResidual actualRetainedFKStock
 unfold OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice
 dsimp only
 rw [map_sub,map_sub,u,v]
 ring

/-- The complete actual residual has a source/reader-controlled bound with original A/beta weights retained. -/
theorem actual_FK_residual_control (n : Nat) (h shift : ℝ) :
 ‖actualFKResidual observation nontrivial half n h shift‖≤
 (‖star (OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2‖*(1/2:ℝ)+
  ‖star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2‖)*
 ‖actualJordanPriceRead observation nontrivial half h shift‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 let price:=actualJordanPriceRead observation nontrivial half h shift
 have u:=price.le_opNorm (OriginalRieszSource.Response.u-actualU n)
 have v:=price.le_opNorm (OriginalRieszSource.Response.v-actualV n)
 have uBound:=actual_source_error_from_eta n
 have vBound:‖OriginalRieszSource.Response.v-actualV n‖≤
  (1/2:ℝ)*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=
  (actual_V_source_error_bound n).trans
   (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left actual_original_source_norm (by positivity)) (by norm_num))
 have normPrice:0≤‖price‖:=ContinuousLinearMap.opNorm_nonneg price
 have uPrice:=u.trans (mul_le_mul_of_nonneg_left uBound normPrice)
 have vPrice:=v.trans (mul_le_mul_of_nonneg_left vBound normPrice)
 unfold actualFKResidual
 dsimp only
 have result:=norm_sub_le
  ((star (OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2)*
   price (OriginalRieszSource.Response.v-actualV n))
  ((star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2)*
   price (OriginalRieszSource.Response.u-actualU n))
 rw [norm_mul,norm_mul] at result
 exact result.trans (by
  have A0 : 0≤‖(star (OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2 : ℂ)‖ := norm_nonneg _
  have B0 : 0≤‖(star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2 : ℂ)‖ := norm_nonneg _
  calc
   _ ≤ ‖star (OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2‖ *
      (‖price‖*((1/2:ℝ)*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖))))+
     ‖star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2‖ *
      (‖price‖*((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖))) :=
    add_le_add (mul_le_mul_of_nonneg_left vPrice A0) (mul_le_mul_of_nonneg_left uPrice B0)
   _ = _ := by ring)

/-- The source-only finite price converges to the actual original FK inventory. -/
theorem actual_finite_FK_price_tendsto (h shift : ℝ) :
 Tendsto (fun n:Nat=>actualFiniteFKPrice observation nontrivial half n h shift) atTop
  (𝓝 (OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice observation nontrivial half h shift)) :=by
 let price:=actualJordanPriceRead observation nontrivial half h shift
 have u:=price.continuous.tendsto _ |>.comp actual_source_tendsto
 have v:=price.continuous.tendsto _ |>.comp actual_V_source_tendsto
 unfold actualFiniteFKPrice
 dsimp only
 let A:ℂ:=star (OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2
 let B:ℂ:=star (OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))/2
 have source:=(v.const_mul A).sub (u.const_mul B) |>.add_const
  (actualRetainedFKStock observation nontrivial half h shift)
 have uPrice:=actual_price_reader_source observation nontrivial half OriginalRieszSource.Response.u h shift
 have vPrice:=actual_price_reader_source observation nontrivial half OriginalRieszSource.Response.v h shift
 change price OriginalRieszSource.Response.u=OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeU h shift at uPrice
 change price OriginalRieszSource.Response.v=OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half OriginalRieszSource.Response.wholeV h shift at vPrice
 have targetPrice : A*price OriginalRieszSource.Response.v-B*price OriginalRieszSource.Response.u+
  actualRetainedFKStock observation nontrivial half h shift=
  OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice observation nontrivial half h shift :=by
  rw [uPrice,vPrice]
  unfold actualRetainedFKStock OriginalKCompactJordanRankSource.actualCompactJordanFKMeanPrice
  dsimp only [A,B]
  ring
 rw [targetPrice] at source
 simpa only [A,B,price,Function.comp_apply] using source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
