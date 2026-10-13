import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSingleReturnEulerRAction.Consumer
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

namespace Native
export OriginalKConstantSeedWholeRAction.ConstantSource (seed)
end Native

/-- The literal quarter gap-Riesz unit is recovered from the already-generated seed norm source. -/
theorem actual_raw_quarter_gap_seed : burnolAmbientGapRieszVector q=(2:ℂ) • Native.seed :=by
 have source:=OriginalKJordanSeedFieldSource.actual_seed_gap_source
 have generated:=congrArg (fun field:BurnolL2=>(2:ℂ) • field) source
 rw [smul_smul] at generated
 norm_num at generated
 exact generated.symm

def actualTailFace (native : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 burnolRadiusMellinTailKernelL2 q (by norm_num) native.value native.rightHalf

/-- Whole normalized tail source is read before P, retaining the true ambient kernel and raw gap seed. -/
theorem actual_whole_quarter_tail_source (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 burnolRadiusNormalizedUnitTail dual q (by norm_num)=
 -(2:ℂ) • burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)+
 ((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed :=by
 dsimp only
 let tail:=actualTailFace coordinate
 have dualTwice:OriginalKQuarterTailPhysicalSource.actualStarSource
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)=coordinate:=by
  cases coordinate
  unfold OriginalKQuarterTailPhysicalSource.actualStarSource
  dsimp only
  congr 1
  exact star_star _
 change -(actualTailFace (OriginalKQuarterTailPhysicalSource.actualStarSource
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate))+
  reflectL2 (actualTailFace (OriginalKQuarterTailPhysicalSource.actualStarSource
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate))))=_
 rw [dualTwice]
 unfold burnolAmbientCompletedMellinKernelFormula burnolAmbientEvenPart
 change -(tail+reflectL2 tail)=
 -(2:ℂ) • ((1/2:ℂ) •
  ((star (burnolMellinGapMoment coordinate.value) • burnolAmbientGapRieszVector q+tail)+
   reflectL2 (star (burnolMellinGapMoment coordinate.value) • burnolAmbientGapRieszVector q+tail)))+
 ((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed
 rw [map_add,map_smul,actual_raw_quarter_gap_seed,map_smul]
 have seedEven:reflectL2 Native.seed=Native.seed:=by
  change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
  rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  rfl
 rw [seedEven]
 module

/-- Actual R acts on the entire original normalized tail source, retaining the native Jordan/seed inventory. -/
theorem actual_quarter_tail_whole_R (coordinate : BurnolCompletedMellinCoordinate) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 burnolDirectRightResolvent z (burnolRadiusNormalizedUnitTail dual q (by norm_num))=
 -(2:ℂ) • OriginalKFourierKernelDependentRAction.actualResonantNativeKernelField coordinate+
 ((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • OriginalKConstantSeedWholeRAction.actualWholeSeedRField dual :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 rw [actual_whole_quarter_tail_source]
 have added:=burnolDirectRightResolvent_sub z right
  (-(2:ℂ) • burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))
  (-(((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed))
 have negative:burnolDirectRightResolvent z
  (-(((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed))=
  -burnolDirectRightResolvent z (((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed) :=by
  rw [←neg_one_smul ℂ (((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • Native.seed),
   burnolDirectRightResolvent_smul,neg_one_smul]
 rw [negative] at added
 simp only [sub_neg_eq_add] at added
 dsimp only [z,dual] at added
 rw [added,burnolDirectRightResolvent_smul,burnolDirectRightResolvent_smul,
  OriginalKFourierKernelDependentRAction.actual_native_kernel_resonant_R,
  OriginalKConstantSeedWholeRAction.actual_original_R_seed_whole_field]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
