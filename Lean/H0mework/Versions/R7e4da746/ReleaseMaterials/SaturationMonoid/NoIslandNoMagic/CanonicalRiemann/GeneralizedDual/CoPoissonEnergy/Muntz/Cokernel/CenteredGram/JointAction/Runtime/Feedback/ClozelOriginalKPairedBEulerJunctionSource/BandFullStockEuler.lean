import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped InnerProductSpace Topology FourierTransform
namespace D
export BandFullStockAction (wholeDebt whole_debt_raw_source whole_debt_projection whole_debt_B_source)
end D
namespace J
export OriginalCommonInverseForcing.SourceJoint (upperSeedFactor upperSourceWave upperSourceWaveAmbient)
end J
namespace Stock
export OriginalCommonInverseForcing.SourceJoint.FullStock (meanDebt)
end Stock
local notation "q" => (1/4:ℝ)
local notation "p" => junctionPoint
local notation "h" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "Eq" => burnolQuarterZeroExtension
private def rate (c:BurnolCompletedMellinCoordinate) : ℂ := star c.value-1/2
local notation "u" => J.upperSeedFactor h
local notation "E" => GapEuler.euler
local notation "DT" => TemperedDistribution ℝ ℂ

/-- The complete two-face complement carrier of the same paired action. -/
def correctionRaw (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 Eq (sourceFirst c:Hq)+fourierL2 (Eq (sourceSecond c:Hq))

private theorem source_action_even (c:BurnolCompletedMellinCoordinate) :
 reflectL2 (sourceAction c)=sourceAction c := by
 unfold sourceAction pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,ContinuousLinearEquiv.coe_coe]
 change reflectL2 ((1/2:ℂ) • (burnolMultiplicativeDilation h (K c:BurnolL2)+
  burnolMultiplicativeDilation (-h) (K c:BurnolL2)))=_
 rw [map_smul,map_add,reflectL2_burnolMultiplicativeDilation,reflectL2_burnolMultiplicativeDilation,
  mem_evenL2ClosedFace_iff.mp (K c).property.2]
 rfl

private theorem correction_piece_even (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
 reflectL2 (Eq (sourceCorrection c i:Hq))=Eq (sourceCorrection c i:Hq) := by
 change reflectL2 (burnolRadiusZeroExtension q (sourceCorrection c i:Hq))=_
 rw [burnolRadiusZeroExtension_reflect,source_correction_even]
 rfl

private theorem correction_raw_even (c:BurnolCompletedMellinCoordinate) :
 reflectL2 (correctionRaw c)=correctionRaw c := by
 unfold correctionRaw
 have first := correction_piece_even c 0
 have second := correction_piece_even c 1
 change reflectL2 (Eq (sourceFirst c:Hq))=Eq (sourceFirst c:Hq) at first
 change reflectL2 (Eq (sourceSecond c:Hq))=Eq (sourceSecond c:Hq) at second
 rw [map_add,first,← fourierL2_reflectL2_commute,second]

private theorem fixed_even_part (value:BurnolL2) (fixed:reflectL2 value=value) :
 burnolAmbientEvenPart value=value := by
 unfold burnolAmbientEvenPart
 rw [fixed]
 module

theorem source_action_projection (c:BurnolCompletedMellinCoordinate) :
 (P (sourceAction c):BurnolL2)=sourceAction c-correctionRaw c := by
 change ((evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto (sourceAction c):BurnolL2)=_
 rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula]
 unfold burnolAmbientExtendedSonineProjectionFormula burnolAmbientEvenMeanZeroCorrection
 unfold burnolAmbientRawMeanZeroCorrection
 change burnolAmbientEvenPart (sourceAction c)-burnolAmbientEvenPart (correctionRaw c)=_
 rw [fixed_even_part _ (source_action_even c),fixed_even_part _ (correction_raw_even c)]

/-- The projected original fees recover their raw carrier together with its actual complete B complement. -/
theorem projected_debt_raw_source (c:BurnolCompletedMellinCoordinate) :
 (P (D.wholeDebt c):BurnolL2)=D.wholeDebt c+(2*u) • correctionRaw c := by
 have positive : 0≤h := junctionShift_pos.le
 have bounded : h≤Real.log 2 := (le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
 have wave : P (J.upperSourceWave c h)=J.upperSourceWaveAmbient c h positive bounded := by
  change (evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto
   (J.upperSourceWaveAmbient c h positive bounded)=_
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 have kernel : P (K c:BurnolL2)=K c := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 have generated := congrArg (fun value:BurnolL2 => (P value:BurnolL2)) (D.whole_debt_raw_source c)
 simp only [map_add,map_sub,map_smul,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul] at generated
 rw [wave,kernel,source_action_projection] at generated
 have raw := D.whole_debt_raw_source c
 change D.wholeDebt c=(J.upperSourceWaveAmbient c h positive bounded:BurnolL2)-
  (2*u) • sourceAction c+(2*u*pairedMellinTranslationCharacter (star c.value) h) • (K c:BurnolL2) at raw
 linear_combination (norm:=module) generated-raw

/-- The two mean charges remain ordinary constant carriers in the regular source action. -/

def contactSource (c:BurnolCompletedMellinCoordinate) : DT :=
 ((p:ℂ)*sourceJump c 0) • (TemperedDistribution.delta p+TemperedDistribution.delta (-p))-
 ((q:ℂ)*sourceTrace c 0) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q))-
 (fourierCLM ℂ DT)
  (((p:ℂ)*sourceJump c 1) • (TemperedDistribution.delta p+TemperedDistribution.delta (-p))-
   ((q:ℂ)*sourceTrace c 1) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q)))

theorem correction_bulk_source (c:BurnolCompletedMellinCoordinate) :
 Eq (sourceBulk c 0)-fourierL2 (Eq (sourceBulk c 1))=
 regularSource c-rate c • correctionRaw c := by
 have full := PsiDrive.source_B_Psi_full_action c
 have first : sourceBulk c 0+rate c • (sourceFirst c:Hq)=
  (BandSourceAction.sourceForce c 0:Hq)+
   (sourceTrace c 0-((p/q:ℝ):ℂ)*sourceJump c 0) • intervalConstant q := full.1
 have second : sourceBulk c 1-rate c • (sourceSecond c:Hq)=
  (BandSourceAction.sourceForce c 1:Hq)+
   (sourceTrace c 1-((p/q:ℝ):ℂ)*sourceJump c 1) • intervalConstant q := full.2
 have positive := congrArg Eq first
 have negative := congrArg (fun value:Hq => fourierL2 (Eq value)) second
 simp only [map_add,map_sub,map_smul] at positive negative
 unfold regularSource correctionRaw
 linear_combination (norm:=module) positive-negative

/-- This computes the source operation before projection, preserving both point contacts and both means. -/
theorem correction_euler_source (c:BurnolCompletedMellinCoordinate) :
 E (correctionRaw c:DT)=(regularSource c:DT)-rate c • (correctionRaw c:DT)+contactSource c := by
 have bulk := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) (correction_bulk_source c)
 simp only [map_sub,map_smul] at bulk
 change (Eq (sourceBulk c 0):DT)-(fourierL2 (Eq (sourceBulk c 1)):DT)=
  (regularSource c:DT)-rate c • (correctionRaw c:DT) at bulk
 have nativeBulk : 𝓕 (Eq (sourceBulk c 1):DT)=(fourierL2 (Eq (sourceBulk c 1)):DT) :=
  Lp.fourier_toTemperedDistribution_eq _
 rw [← nativeBulk] at bulk
 have first := source_weak_euler c 0
 have second := congrArg (fourierCLM ℂ DT) (source_weak_euler c 1)
 simp only [map_add,map_sub,map_smul,fourierCLM_apply] at second
 have native : (correctionRaw c:DT)=(Eq (sourceFirst c:Hq):DT)+𝓕 (Eq (sourceSecond c:Hq):DT) := by
  change (Lp.toTemperedDistributionCLM ℂ volume 2)
   (Eq (sourceFirst c:Hq)+fourierL2 (Eq (sourceSecond c:Hq)))=_
  rw [map_add]
  have secondNative : 𝓕 (Eq (sourceSecond c:Hq):DT)=(fourierL2 (Eq (sourceSecond c:Hq)):DT) :=
   Lp.fourier_toTemperedDistribution_eq _
  change (Eq (sourceFirst c:Hq):DT)+(fourierL2 (Eq (sourceSecond c:Hq)):DT)=_
  rw [← secondNative]
 conv_lhs => rw [native]
 rw [map_add,GapEuler.euler_fourier]
 unfold contactSource
 simp only [map_add,map_sub,map_smul,fourierCLM_apply]
 change E (Eq (sourceCorrection c 0:Hq):DT)-𝓕 (E (Eq (sourceCorrection c 1:Hq):DT))=_
 linear_combination (norm:=module) first-second+bulk

/-- The actual projected correction plus the actual mean debt now has one complete source Euler equation. -/
theorem actual_projected_debt_euler (c:BurnolCompletedMellinCoordinate) :
 E (((P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection c h)+u • Stock.meanDebt c h:BurnolPaAmbientCarrier):BurnolL2):DT)+
 rate c • (((P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection c h)+u • Stock.meanDebt c h:BurnolPaAmbientCarrier):BurnolL2):DT)=
 E (D.wholeDebt c:DT)+rate c • (D.wholeDebt c:DT)+
  (2*u) • ((regularSource c:DT)+contactSource c) := by
 have literal : ((P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection c h)+
   u • Stock.meanDebt c h:BurnolPaAmbientCarrier):BurnolL2)=
   D.wholeDebt c+(2*u) • correctionRaw c := by
  rw [← D.whole_debt_projection]
  exact projected_debt_raw_source c
 have native := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2) literal
 simp only [map_add,map_smul] at native
 change (((P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection c h)+
  u • Stock.meanDebt c h:BurnolPaAmbientCarrier):BurnolL2):DT)=
  (D.wholeDebt c:DT)+(2*u) • (correctionRaw c:DT) at native
 rw [native,map_add,map_smul,correction_euler_source]
 module

/-- These are the two actual inverse fibres of the complete raw fee carrier. -/
def debtFiber (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
 ![burnolAmbientMeanZeroFirstCorrection (D.wholeDebt c),
   burnolAmbientMeanZeroSecondCorrection (D.wholeDebt c)] i

/-- The original complex four-mouth action is consumed by the actual full-stock source fibres. -/
theorem actual_debt_B_matrix (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 (star (PsiDrive.sourceRate c i)+PsiDrive.sourceRate c j)*inner ℂ (debtFiber c i) (debtFiber c j)=
 inner ℂ ((-2*u) • BandSourceAction.sourceForce c i) (debtFiber c j)+
 inner ℂ (debtFiber c i) ((-2*u) • BandSourceAction.sourceForce c j)-
  (star (-2*u)*(-2*u))*BandSourceAction.chargeGram c i j := by
 have same (k:Fin 2) : debtFiber c k=(-2*u) • sourceCorrection c k := by
  fin_cases k
  · exact (D.whole_debt_B_source c).1
  · exact (D.whole_debt_B_source c).2
 rw [same i,same j]
 simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]
 linear_combination (star (-2*u)*(-2*u))*BandSourceAction.paired_source_matrix_action c i j

/-- The original zero-owned Pa source annihilates its actual wave and feeds the exact finite-price scalar. -/
theorem actual_projected_debt_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 inner ℂ (K c) (P (OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection c h)+
   u • Stock.meanDebt c h)=u*star (BandFiniteSourcePrice.finiteSourcePrice c h) := by
 have positive : 0≤h := junctionShift_pos.le
 have bounded : h≤Real.log 2 := (le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small
 have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
 have member := OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h positive bounded
 have wave := inner_eq_zero_symm.mp
  ((burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal
   (J.upperSourceWaveAmbient c h positive bounded) member)
 change inner ℂ (K c:BurnolL2) (J.upperSourceWave c h)=0 at wave
 have forcing : inner ℂ (K c:BurnolL2)
   (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))=
   -star (BandFiniteSourcePrice.finiteSourcePrice c h) := by
  calc
   _=star (inner ℂ (OriginalRieszFiniteSource.forcingIntegral c h+
     OriginalRieszFiniteSource.forcingIntegral c (-h)) (K c:BurnolL2)) := (inner_conj_symm _ _).symm
   _=_ := by
    rw [OriginalRieszFinitePairing.forcing_pair_source c h positive,
     BandFiniteSourcePrice.source_pair_finite_price c h positive,star_neg]
 rw [inner_add_right] at forcing
 have action := congrArg (fun value:BurnolL2 => inner ℂ (K c:BurnolL2) value)
  (BandFullStockAction.paired_original_source_action c)
 simp only [inner_add_right,inner_smul_right] at action
 have debt : inner ℂ (K c:BurnolL2) (D.wholeDebt c)=u*star (BandFiniteSourcePrice.finiteSourcePrice c h) := by
  rw [D.whole_debt_raw_source]
  simp only [inner_add_right,inner_sub_right,inner_smul_right]
  rw [wave,action,forcing]
  ring
 rw [← D.whole_debt_projection]
 exact ((evenBurnolClosedFace q).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
  (K c) (D.wholeDebt c)).trans debt

end OriginalKPairedBEulerJunctionSource.BandFullStockEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
