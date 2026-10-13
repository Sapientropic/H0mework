import Lean
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Quarter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
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



elab "paid172QuarterPhysicalPrice" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPositionQuarterFTCAction.Price".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPositionQuarterFTCAction.actual_physical_quarter_source_price".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

local instance compactSourcePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The new compact source uses the actual adjoint/Fourier directions on the given physical material. -/
theorem actual_compact_F_R_physical_action (coordinate : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (material : BurnolPaAmbientCarrier) :
 inner ℂ (fourierL2 source) (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))=
 inner ℂ (burnolDirectRightResolvent ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) source)
   (fourierL2 (material : BurnolL2)) := by
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have starRight : 1/4<((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2).re := by
  rw [Complex.div_re];norm_num;linarith [(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).rightHalf]
 have sourceAction:=actual_original_R_adjoint (coordinate.value/2) right (fourierL2 source) (material : BurnolL2)
 simp only [star_div₀,star_ofNat] at sourceAction
 have reverse:=FiniteMobiusResolventFlux.fourier_R
   ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) starRight source
 change fourierL2 (burnolDirectRightResolvent ((star coordinate.value)/2) source)=
   Paid.Rplus ((star coordinate.value)/2) (fourierL2 source) at reverse
 rw [←reverse] at sourceAction
 have twice : fourierL2 (fourierL2 (material : BurnolL2))=(material : BurnolL2) := by
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp material.property.2
 have moved:=fourierL2.inner_map_map
   (burnolDirectRightResolvent ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) source)
   (fourierL2 (material : BurnolL2))
 rw [twice] at moved
 exact sourceAction.trans moved

/-- Actual projected qtail keeps the original dual Riesz and G response, using only the receiver's own physical qualification. -/
theorem actual_compact_tail_physical_price (coordinate : BurnolCompletedMellinCoordinate)
 (physical : BurnolPaAmbientCarrier) :
 inner ℂ (burnolRadiusNormalizedUnitTail (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate) q (by norm_num))
   (physical : BurnolL2)=
 -(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) physical+
 (2:ℂ)*burnolMellinGapMoment coordinate.value*Paid.actualMean (physical : BurnolL2) := by
 have source:=OriginalKQuarterTailPhysicalSource.actual_quarter_tail_physical_source
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)
 have dualtwice : OriginalKQuarterTailPhysicalSource.actualStarSource
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)=coordinate := by
  cases coordinate
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 rw [dualtwice] at source
 have read:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
   |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical
     (burnolRadiusNormalizedUnitTail (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate) q (by norm_num))
 change inner ℂ (burnolEvenAmbientProjection _) physical=inner ℂ _ (physical : BurnolL2) at read
 rw [←read,source,inner_add_left,inner_smul_left,inner_smul_left,
   OriginalRieszFiniteSynthesis.gapMeanVector_readback]
 simp only [starRingEnd_apply,star_neg,star_mul,star_ofNat,star_star]
 change -(2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector coordinate) physical+
   burnolMellinGapMoment coordinate.value*2*Paid.actualMean (physical : BurnolL2)=_
 ring

/-- Compact source quarter response is generated by its own rank/FTC law and a source-admitted rate. -/
theorem actual_compact_quarter_mean_price (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 Paid.actualMean (burnolDirectRightResolvent (coordinate.value/2) source)=
 (actualCompactTailCoefficient coordinate source*(((2*q:ℝ):ℂ)*(q:ℂ)^(-coordinate.value))-
   Paid.actualMean source)/(coordinate.value/2-1/2) := by
 have generated:=actual_compact_quarter_mean_action coordinate source compact even
 have qualified : coordinate.value/2-1/2≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  norm_num [Complex.div_re] at real
  linarith [coordinate.belowOne]
 apply (eq_div_iff qualified).mpr
 linear_combination generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
