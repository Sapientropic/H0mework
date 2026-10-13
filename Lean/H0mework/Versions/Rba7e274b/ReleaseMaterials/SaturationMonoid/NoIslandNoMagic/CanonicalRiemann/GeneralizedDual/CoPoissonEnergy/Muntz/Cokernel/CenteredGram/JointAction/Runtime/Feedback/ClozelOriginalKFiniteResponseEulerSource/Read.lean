import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
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

theorem actual_finite_whole_UV_qualification (n : Nat) :
 originalPhysicalCutoff q (actualWholeU n)=actualWholeU n ∧
 reflectL2 (actualWholeU n)=actualWholeU n ∧
 originalPhysicalCutoff q (actualWholeV n)=actualWholeV n ∧
 reflectL2 (actualWholeV n)=actualWholeV n :=by
 refine ⟨?_,?_,?_,?_⟩
 · change burnolRadiusZeroExtension q (burnolRadiusRestriction q
   (burnolRadiusZeroExtension q (Prior.actualU n:BurnolQuarterIntervalL2)))=_
   rw [burnolRadiusRestriction_zeroExtension]
   rfl
 · change reflectL2 (burnolRadiusZeroExtension q (Prior.actualU n:BurnolQuarterIntervalL2))=_
   rw [burnolRadiusZeroExtension_reflect,actual_U_even]
   rfl
 · change burnolRadiusZeroExtension q (burnolRadiusRestriction q
   (burnolRadiusZeroExtension q (Prior.actualV n:BurnolQuarterIntervalL2)))=_
   rw [burnolRadiusRestriction_zeroExtension]
   rfl
 · change reflectL2 (burnolRadiusZeroExtension q (Prior.actualV n:BurnolQuarterIntervalL2))=_
   rw [burnolRadiusZeroExtension_reflect,actual_V_even]
   rfl

/-- Actual finite U field and its own physical Jordan read are consumed by the existing source-only price reader. -/
theorem actual_finite_U_Jordan_read (n : Nat) (h shift : ℝ) (nonnegative : 0≤shift) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 OriginalKResponseCofinalSourceAction.actualJordanPriceRead observation nontrivial half h shift (Prior.actualU n)=
 actualFiniteEulerJordanPrice dual (actualWholeU n) material :=by
 dsimp only
 have source:=OriginalKResponseCofinalSourceAction.actual_price_reader_source observation nontrivial half (Prior.actualU n) h shift
 have fields:=actual_finite_whole_UV_qualification n
 have price:=OriginalKCompactJordanRankSource.actual_compact_Jordan_physical_price
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualWholeU n) fields.1 fields.2.1
  (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)
 dsimp only at price
 have native:=OriginalKCompactJordanRankSource.actual_native_tail_R_price observation nontrivial half h shift nonnegative
 have equality:OriginalKCompactJordanRankSource.actualCompactJordanPrice
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualWholeU n)
  (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)=
  OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half (actualWholeU n) h shift :=by
  unfold OriginalKCompactJordanRankSource.actualCompactJordanPrice OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice
  dsimp only
  rw [native]
 unfold actualFiniteEulerJordanPrice
 rw [actual_Jordan_action_source]
 exact source.trans (equality.symm.trans price.symm)

theorem actual_finite_V_Jordan_read (n : Nat) (h shift : ℝ) (nonnegative : 0≤shift) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 OriginalKResponseCofinalSourceAction.actualJordanPriceRead observation nontrivial half h shift (Prior.actualV n)=
 actualFiniteEulerJordanPrice dual (actualWholeV n) material :=by
 dsimp only
 have source:=OriginalKResponseCofinalSourceAction.actual_price_reader_source observation nontrivial half (Prior.actualV n) h shift
 have fields:=actual_finite_whole_UV_qualification n
 have price:=OriginalKCompactJordanRankSource.actual_compact_Jordan_physical_price
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualWholeV n) fields.2.2.1 fields.2.2.2
  (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)
 dsimp only at price
 have native:=OriginalKCompactJordanRankSource.actual_native_tail_R_price observation nontrivial half h shift nonnegative
 have equality:OriginalKCompactJordanRankSource.actualCompactJordanPrice
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (actualWholeV n)
  (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h)=
  OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice observation nontrivial half (actualWholeV n) h shift :=by
  unfold OriginalKCompactJordanRankSource.actualCompactJordanPrice OriginalKCompactJordanRankSource.actualNativeCompactJordanPrice
  dsimp only
  rw [native]
 unfold actualFiniteEulerJordanPrice
 rw [actual_Jordan_action_source]
 exact source.trans (equality.symm.trans price.symm)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
