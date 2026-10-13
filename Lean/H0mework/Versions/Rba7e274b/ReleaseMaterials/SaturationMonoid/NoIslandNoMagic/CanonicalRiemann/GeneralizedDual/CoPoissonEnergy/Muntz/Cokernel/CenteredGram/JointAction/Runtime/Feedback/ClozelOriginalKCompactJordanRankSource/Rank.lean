import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactJordanRankSource.Source
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

private theorem actual_R_source_even (z : ℂ) (source : BurnolL2) (even : reflectL2 source=source) :
 reflectL2 (burnolDirectRightResolvent z source)=burnolDirectRightResolvent z source :=by
 unfold burnolDirectRightResolvent
 rw [map_neg]
 have mapped:reflectL2 (∫ time:ℝ in Ioi 0,burnolDirectRightResolventIntegrand z source time)=
  ∫ time:ℝ in Ioi 0,reflectL2 (burnolDirectRightResolventIntegrand z source time):=
  (LinearIsometry.integral_comp_comm reflectL2 (burnolDirectRightResolventIntegrand z source)
   (μ:=volume.restrict (Ioi 0))).symm
 rw [mapped]
 congr 1
 apply setIntegral_congr_fun measurableSet_Ioi
 intro time _
 unfold burnolDirectRightResolventIntegrand
 dsimp only
 rw [map_smul,reflectL2_burnolMultiplicativeDilation,even]

private theorem actual_quarter_cut_even (source : BurnolL2) (even : reflectL2 source=source) :
 reflectL2 (originalPhysicalCutoff q source)=originalPhysicalCutoff q source :=by
 unfold originalPhysicalCutoff
 rw [burnolRadiusZeroExtension_reflect]
 change burnolRadiusZeroExtension q (reflectRestricted q (restrictToInterval q source))=_
 rw [←restrictToInterval_reflectL2,even]
 rfl

def actualFirstCut (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2) : BurnolL2 :=
 originalPhysicalCutoff q
  (burnolDirectRightResolvent ((OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2) source)

/-- The first actual R update produces its own complete compact/even qualification, without physical or terminal input. -/
theorem actual_first_cut_qualification (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (even : reflectL2 source=source) :
 originalPhysicalCutoff q (actualFirstCut coordinate source)=actualFirstCut coordinate source ∧
 reflectL2 (actualFirstCut coordinate source)=actualFirstCut coordinate source :=by
 constructor
 · unfold actualFirstCut originalPhysicalCutoff
   rw [burnolRadiusRestriction_zeroExtension]
 · exact actual_quarter_cut_even _ (actual_R_source_even _ source even)

/-- A second genuine R consumes the first generated compact source and the entire original normalized tail. -/
theorem actual_compact_Jordan_rank_source (coordinate : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 OriginalKFourierKernelDependentRAction.actualResonantField z source=
 originalPhysicalCutoff q (burnolDirectRightResolvent z (actualFirstCut coordinate source))+
 OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual (actualFirstCut coordinate source) •
  burnolRadiusNormalizedUnitTail dual q (by norm_num)+
 OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
  (-(2:ℂ) • OriginalKFourierKernelDependentRAction.actualResonantNativeKernelField coordinate+
   ((4:ℂ)*star (burnolMellinGapMoment coordinate.value)) • OriginalKConstantSeedWholeRAction.actualWholeSeedRField dual) :=by
 dsimp only
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 have first:=OriginalKCompactAdjointRSource.actual_compact_R_rank_source dual source compact even
 have qualification:=actual_first_cut_qualification coordinate source even
 have second:=OriginalKCompactAdjointRSource.actual_compact_R_rank_source dual (actualFirstCut coordinate source)
  qualification.1 qualification.2
 rw [←OriginalKFourierKernelDependentRAction.actual_resonant_repeated_R z right]
 rw [first]
 have mapped:=burnolDirectRightResolvent_sub z right (actualFirstCut coordinate source)
  (-(OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
   burnolRadiusNormalizedUnitTail dual q (by norm_num)))
 have negative:burnolDirectRightResolvent z
  (-(OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
   burnolRadiusNormalizedUnitTail dual q (by norm_num)))=
  -burnolDirectRightResolvent z (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
   burnolRadiusNormalizedUnitTail dual q (by norm_num)) :=by
  rw [←neg_one_smul ℂ (OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
   burnolRadiusNormalizedUnitTail dual q (by norm_num)),burnolDirectRightResolvent_smul,neg_one_smul]
 rw [negative] at mapped
 simp only [sub_neg_eq_add] at mapped
 change burnolDirectRightResolvent z (actualFirstCut coordinate source+
  OriginalKCompactAdjointRSource.actualCompactTailCoefficient dual source •
   burnolRadiusNormalizedUnitTail dual q (by norm_num))=_
 rw [mapped]
 nth_rw 1 [second]
 rw [burnolDirectRightResolvent_smul,actual_quarter_tail_whole_R]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactJordanRankSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
