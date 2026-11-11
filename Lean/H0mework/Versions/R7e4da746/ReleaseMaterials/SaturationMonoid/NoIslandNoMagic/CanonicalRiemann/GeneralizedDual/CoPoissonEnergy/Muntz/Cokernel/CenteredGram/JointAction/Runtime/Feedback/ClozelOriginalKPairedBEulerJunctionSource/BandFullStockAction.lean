import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandSourceAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FullStock.Boundary

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandFullStockAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalRieszFiniteSource
open OriginalPaPhysicalGreen OriginalRieszFiniteSynthesis
open scoped InnerProductSpace Topology
namespace J
export OriginalCommonInverseForcing.SourceJoint
 (upperSeedFactor upperSourceWave upperSourceWaveAmbient upperSourceCorrection upperSourceField
  actual_upper_common_seed)
end J
namespace Stock
export OriginalCommonInverseForcing.SourceJoint.FullStock (meanDebt actual_inside_mean_debt)
end Stock
local notation "q" => (1/4:ℝ)
local notation "h" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "u" => J.upperSeedFactor h

private theorem h_nonnegative : 0 ≤ h := junctionShift_pos.le
private theorem h_bounded : h ≤ Real.log 2 := (le_abs_self _).trans fixedShift_small

/-- The complete inside carrier is retained before its projected mean read. -/
def insideSource (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 (positionColumn c h+originalPhysicalCutoff q (positionColumn c (-h)))+
 fourierL2 (fourierColumn c (-h)+originalPhysicalCutoff q (fourierColumn c h))

/-- Both original fees are restrictions of this one actual raw source. -/
def wholeDebt (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 J.upperSourceCorrection c h-u • insideSource c

theorem forcing_whole_carrier (c:BurnolCompletedMellinCoordinate) :
 forcingIntegral c h+forcingIntegral c (-h)=
 (CoPoisson.positionSeed c h+fourierL2 (CoPoisson.fourierSeed c h))+insideSource c := by
 rw [CoPoisson.positionSeed_eq_exterior c h h_nonnegative,
  CoPoisson.fourierSeed_eq_exterior c h h_nonnegative,
  forcingIntegral_columns,forcingIntegral_columns]
 unfold insideSource
 rw [map_sub,map_add]
 module

private theorem physical_fourier_projection (value:BurnolL2) : P (fourierL2 value)=F (P value) := by
 apply ext_inner_right ℂ
 intro test
 have left := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_right test (fourierL2 value)
 have right := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_right (F test) value
 change inner ℂ (P (fourierL2 value)) test=inner ℂ (fourierL2 value) (test:BurnolL2) at left
 change inner ℂ (P value) (F test)=inner ℂ value (F test:BurnolL2) at right
 rw [left,OriginalRieszFiniteSynthesis.fourier_pairing,right]
 have even := mem_evenL2ClosedFace_iff.mp test.property.2
 have twice : fourierL2 (fourierL2 (test:BurnolL2))=test := by rw [fourierL2_fourierL2,even]
 have paired := fourierL2.inner_map_map value (fourierL2 (test:BurnolL2))
 rwa [twice] at paired

theorem inside_projection (c:BurnolCompletedMellinCoordinate) :
 P (insideSource c)=-Stock.meanDebt c h := by
 unfold insideSource
 rw [map_add,physical_fourier_projection]
 exact Stock.actual_inside_mean_debt c h h_nonnegative

/-- The projected complete raw debt is exactly the two original full-stock fees. -/
theorem whole_debt_projection (c:BurnolCompletedMellinCoordinate) :
 P (wholeDebt c)=P (J.upperSourceCorrection c h)+u • Stock.meanDebt c h := by
 unfold wholeDebt
 rw [map_sub,map_smul,inside_projection]
 module

theorem paired_original_source_action (c:BurnolCompletedMellinCoordinate) :
 sourceAction c=pairedMellinTranslationCharacter (star c.value) h • (K c:BurnolL2)+
 (1/2:ℂ) • (forcingIntegral c h+forcingIntegral c (-h)) := by
 have inverse : fullMellinTranslationCharacter (star c.value) (-h)=
   reciprocalMellinTranslationCharacter (star c.value) h := by
  unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
  congr 1
  push_cast
  ring
 unfold sourceAction pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,ContinuousLinearEquiv.coe_coe]
 change (1/2:ℂ) • (burnolMultiplicativeDilation h (K c:BurnolL2)+
  burnolMultiplicativeDilation (-h) (K c:BurnolL2))=_
 rw [original_finite_action,original_finite_action,inverse]
 unfold pairedMellinTranslationCharacter
 module

/-- No price is an input: this equation is computed from both literal source actions and inside columns. -/
theorem whole_debt_raw_source (c:BurnolCompletedMellinCoordinate) :
 wholeDebt c=J.upperSourceWave c h-(2*u) • sourceAction c+
  (2*u*pairedMellinTranslationCharacter (star c.value) h) • (K c:BurnolL2) := by
 have raw : wholeDebt c=J.upperSourceWave c h-u • (forcingIntegral c h+forcingIntegral c (-h)) := by
  unfold wholeDebt J.upperSourceCorrection
  rw [J.actual_upper_common_seed c h h_nonnegative,forcing_whole_carrier]
  module
 rw [raw,paired_original_source_action]
 module

private def evenMap : BurnolL2 →L[ℂ] BurnolL2 :=
 (1/2:ℂ) • (ContinuousLinearMap.id ℂ BurnolL2+reflectL2.toContinuousLinearMap)
private def positionMap : BurnolL2 →L[ℂ] M :=
 burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
  (burnolQuarterRestriction.comp evenMap)
private def fourierMap : BurnolL2 →L[ℂ] M :=
 burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
  (burnolQuarterRestriction.comp (fourierL2.toLinearIsometry.toContinuousLinearMap.comp evenMap))
private def firstMap : BurnolL2 →L[ℂ] M :=
 burnolMeanZeroBlockInverse.comp (positionMap-burnolMeanZeroTruncatedFourier.comp fourierMap)
private def secondMap : BurnolL2 →L[ℂ] M :=
 fourierMap-burnolMeanZeroTruncatedFourier.comp firstMap

private theorem first_map_source (value:BurnolL2) :
 firstMap value=burnolAmbientMeanZeroFirstCorrection value := rfl
private theorem second_map_source (value:BurnolL2) :
 secondMap value=burnolAmbientMeanZeroSecondCorrection value := rfl

private theorem physical_block_zero (value:BurnolPaAmbientCarrier) :
 positionMap (value:BurnolL2)=0 ∧ fourierMap (value:BurnolL2)=0 := by
 have fixed : burnolAmbientEvenPart (value:BurnolL2)=value := by
  unfold burnolAmbientEvenPart
  rw [mem_evenL2ClosedFace_iff.mp value.property.2]
  module
 constructor
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolAmbientEvenPart (value:BurnolL2)))=0
   rw [fixed]
   exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr value.property.1.1
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection
    (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenPart (value:BurnolL2))))=0
   rw [fixed]
   exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr value.property.1.2

private theorem physical_first_zero (value:BurnolPaAmbientCarrier) : firstMap (value:BurnolL2)=0 := by
 have zero := physical_block_zero value
 change burnolMeanZeroBlockInverse (positionMap (value:BurnolL2)-
   burnolMeanZeroTruncatedFourier (fourierMap (value:BurnolL2)))=0
 rw [zero.1,zero.2,map_zero,sub_zero,map_zero]

private theorem physical_second_zero (value:BurnolPaAmbientCarrier) : secondMap (value:BurnolL2)=0 := by
 change fourierMap (value:BurnolL2)-burnolMeanZeroTruncatedFourier (firstMap (value:BurnolL2))=0
 rw [(physical_block_zero value).2,physical_first_zero,map_zero,sub_zero]

/-- The two full-stock fees retain their actual B inverse fibres before projection. -/
theorem whole_debt_B_source (c:BurnolCompletedMellinCoordinate) :
 burnolAmbientMeanZeroFirstCorrection (wholeDebt c)=(-2*u) • sourceFirst c ∧
 burnolAmbientMeanZeroSecondCorrection (wholeDebt c)=(-2*u) • sourceSecond c := by
 have waveFirst := physical_first_zero (J.upperSourceWaveAmbient c h h_nonnegative h_bounded)
 have waveSecond := physical_second_zero (J.upperSourceWaveAmbient c h h_nonnegative h_bounded)
 change firstMap (J.upperSourceWave c h)=0 at waveFirst
 change secondMap (J.upperSourceWave c h)=0 at waveSecond
 have kernelFirst := physical_first_zero (K c)
 have kernelSecond := physical_second_zero (K c)
 constructor
 · change firstMap (wholeDebt c)=(-2*u) • firstMap (sourceAction c)
   rw [whole_debt_raw_source,map_add,map_sub,map_smul,map_smul,waveFirst,kernelFirst,smul_zero,add_zero,zero_sub]
   module
 · change secondMap (wholeDebt c)=(-2*u) • secondMap (sourceAction c)
   rw [whole_debt_raw_source,map_add,map_sub,map_smul,map_smul,waveSecond,kernelSecond,smul_zero,add_zero,zero_sub]
   module

/-- The actual first B fibre now consumes the original complete Euler bulk and both delta contacts. -/
theorem whole_debt_first_euler (c:BurnolCompletedMellinCoordinate) :
 GapEuler.euler (burnolQuarterZeroExtension
   (burnolAmbientMeanZeroFirstCorrection (wholeDebt c):Hq):TemperedDistribution ℝ ℂ)=
 (-2*u) • ((burnolQuarterZeroExtension (sourceBulk c 0):TemperedDistribution ℝ ℂ)+
  ((junctionPoint:ℂ)*sourceJump c 0) •
   (TemperedDistribution.delta junctionPoint+TemperedDistribution.delta (-junctionPoint))-
  ((q:ℂ)*sourceTrace c 0) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q))) := by
 rw [(whole_debt_B_source c).1]
 simp only [Submodule.coe_smul]
 change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
  (burnolQuarterZeroExtension ((-2*u) • (sourceFirst c:Hq))))=_
 rw [map_smul,map_smul,map_smul]
 exact congrArg (fun value:TemperedDistribution ℝ ℂ => (-2*u) • value) (source_weak_euler c 0)

/-- The second physical face has the same source scale, with its own endpoint and internal jump. -/
theorem whole_debt_second_euler (c:BurnolCompletedMellinCoordinate) :
 GapEuler.euler (burnolQuarterZeroExtension
   (burnolAmbientMeanZeroSecondCorrection (wholeDebt c):Hq):TemperedDistribution ℝ ℂ)=
 (-2*u) • ((burnolQuarterZeroExtension (sourceBulk c 1):TemperedDistribution ℝ ℂ)+
  ((junctionPoint:ℂ)*sourceJump c 1) •
   (TemperedDistribution.delta junctionPoint+TemperedDistribution.delta (-junctionPoint))-
  ((q:ℂ)*sourceTrace c 1) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q))) := by
 rw [(whole_debt_B_source c).2]
 simp only [Submodule.coe_smul]
 change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
  (burnolQuarterZeroExtension ((-2*u) • (sourceSecond c:Hq))))=_
 rw [map_smul,map_smul,map_smul]
 exact congrArg (fun value:TemperedDistribution ℝ ℂ => (-2*u) • value) (source_weak_euler c 1)

end OriginalKPairedBEulerJunctionSource.BandFullStockAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
