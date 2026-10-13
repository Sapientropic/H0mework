import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactJordanRankSource.Rank
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

private theorem actual_mean_quarter_cut (source : BurnolL2) :
 Paid.actualMean (originalPhysicalCutoff q source)=Paid.actualMean source :=by
 unfold Paid.actualMean originalPhysicalCutoff
 change ((‖intervalConstant q‖^2:ℂ)⁻¹)*inner ℂ (intervalConstant q)
  (burnolRadiusRestriction q (burnolRadiusZeroExtension q (burnolRadiusRestriction q source)))=_
 rw [burnolRadiusRestriction_zeroExtension]
 rfl

def actualFirstMean (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source*
  (((2*q:ℝ):ℂ)*(q:ℂ)^(-dual.value))-Paid.actualMean source)/(dual.value/2-1/2)

def actualSecondMean (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2) : ℂ :=
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual (actualFirstCut coordinate source)*
  (((2*q:ℝ):ℂ)*(q:ℂ)^(-dual.value))-actualFirstMean coordinate source)/(dual.value/2-1/2)

/-- The first generated R restriction retains its actual source mean and tail coefficient. -/
theorem actual_first_cut_mean (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 Paid.actualMean (actualFirstCut coordinate source)=actualFirstMean coordinate source :=by
 unfold actualFirstCut
 rw [actual_mean_quarter_cut,OriginalKCompactAdjointRSource.actual_compact_quarter_mean_price _ source compact even]
 rfl

/-- Source-qualified second R consumes that exact generated first mean, rather than projecting away its stock. -/
theorem actual_second_R_mean (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 Paid.actualMean (burnolDirectRightResolvent ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2)
  (actualFirstCut coordinate source))=actualSecondMean coordinate source :=by
 have qualification:=actual_first_cut_qualification coordinate source even
 rw [OriginalKCompactAdjointRSource.actual_compact_quarter_mean_price _ _ qualification.1 qualification.2,
  actual_first_cut_mean coordinate source compact even]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
