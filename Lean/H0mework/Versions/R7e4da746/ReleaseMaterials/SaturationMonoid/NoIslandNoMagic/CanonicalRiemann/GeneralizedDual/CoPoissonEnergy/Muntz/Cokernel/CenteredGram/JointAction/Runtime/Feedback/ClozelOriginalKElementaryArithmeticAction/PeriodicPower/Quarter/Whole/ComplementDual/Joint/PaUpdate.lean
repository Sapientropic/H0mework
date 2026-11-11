import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open scoped Topology
open private tate_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa
local notation "q"=>(1/4:ℝ)
local notation "T"=>burnolTateReciprocalL2
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem even_eq_of_positive (left right:BurnolL2)
    (leftEven:reflectL2 left=left) (rightEven:reflectL2 right=right)
    (positive:∀ᵐx:ℝ∂volume,∀_positive:0<x,left x=right x):left=right:=by
  apply Lp.ext
  filter_upwards [positive,negMeasurePreserving.quasiMeasurePreserving.ae positive,
    Lp.coeFn_compMeasurePreserving left negMeasurePreserving,
    Lp.coeFn_compMeasurePreserving right negMeasurePreserving,volume.ae_ne (0:ℝ)]
    with x first second leftReflection rightReflection nonzero
  change reflectL2 left x=left (-x) at leftReflection
  change reflectL2 right x=right (-x) at rightReflection
  rw [leftEven] at leftReflection
  rw [rightEven] at rightReflection
  by_cases pos:0<x
  · exact first pos
  · have negpos:0< -x:=by have negative:=lt_of_le_of_ne (le_of_not_gt pos) nonzero;linarith
    exact leftReflection.trans ((second negpos).trans rightReflection.symm)

def shellSource (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  T (burnolMobiusSourceL2 (volterraPhysicalShell (barC c) 4))

def forcingCoefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  -2*burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf (tateSource c j)

def unitPa (c:BurnolCompletedMellinCoordinate):BurnolPaAmbientCarrier:=
  burnolPaSourceCorrection (barC c)
    ⟨volterraPhysicalShell (barC c) 4,volterraPhysicalShell_mem _ _⟩

private theorem residual_even (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    reflectL2 (residualSource c j)=residualSource c j:=by
  have even:=tate_even c j
  rw [residualSource,map_sub,sourceVolterraResolvent_reflect,even,
    sourceVolterraWindow_even _ _ (sourceAnnulusCut_even _ even)]

/-- The remaining annulus source is exactly one original shell source, with its full actual upper contact. -/
theorem actual_residual_shell_source (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    A (residualSource c j)=forcingCoefficient c j • shellSource c:=by
  apply even_eq_of_positive _ _ (sourceAnnulusCut_even _ (residual_even c j))
    (by rw [map_smul];exact congrArg (forcingCoefficient c j • ·) (original_tate_source_even _))
  filter_upwards [sourceAnnulusCut_coeFn (residualSource c j),actual_residual_source_profile c j,
    volterraPhysicalShell_tate_source_raw (barC c) 4 (by norm_num),
    Lp.coeFn_smul (forcingCoefficient c j) (shellSource c),volume.ae_ne q,volume.ae_ne (4:ℝ)]
    with x cut residual shell scalar notQuarter notFour positive
  change T (burnolMobiusSourceL2 (volterraPhysicalShell (barC c) 4)) x=_ at shell
  change (forcingCoefficient c j • shellSource c:BurnolL2) x=_ at scalar
  rw [cut,scalar,Pi.smul_apply,smul_eq_mul]
  change (if q < |x| ∧ |x|≤4 then residualSource c j x else 0)=forcingCoefficient c j*
    T (burnolMobiusSourceL2 (volterraPhysicalShell (barC c) 4)) x
  rw [shell,abs_of_pos positive]
  by_cases band:q<x∧x≤4
  · have before:x<4:=lt_of_le_of_ne band.2 notFour
    rw [if_pos band,if_pos (show x∈Ico q 4 from ⟨band.1.le,before⟩),
      residual positive,if_pos band,forcingCoefficient]
    ring
  · have outside:x∉Ico q 4:=by
      intro inside
      exact band ⟨lt_of_le_of_ne inside.1 notQuarter.symm,inside.2.le⟩
    rw [if_neg band,if_neg outside,mul_zero]

private theorem window_cut (d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    A (sourceVolterraWindow d value)=sourceVolterraWindow d value:=
  sourceAnnulusCut_idempotent _

/-- The next actual Pa is generated by the original R correction and the one original shell correction. -/
theorem actual_next_pa (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    actualPa c (j+1)=
      burnolPaSourceCorrection (barC c) ⟨actualPa c j,actual_pa_mem c j⟩+
        forcingCoefficient c j • unitPa c:=by
  have unitMem:unitPa c∈burnolCompactCoPoissonClosedRange:=burnolPaSourceCorrection_mem _ _
  have correctedMem:=burnolPaSourceCorrection_mem (barC c) ⟨actualPa c j,actual_pa_mem c j⟩
  apply original_pa_tate_source_injective _ _ (actual_pa_mem c (j+1))
    (burnolCompactCoPoissonClosedRange.toSubmodule.add_mem correctedMem
      (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ unitMem))
  have corrected: T (burnolMobiusSourceL2
      (burnolPaSourceCorrection (barC c) ⟨actualPa c j,actual_pa_mem c j⟩))=
      sourceVolterraWindow (barC c)
        (sourceVolterraWindow (barC c) (A (tateSource c j))):=by
    rw [←sourceVolterraWindow_original_pa (barC c) (actualPa c j) (actual_pa_mem c j),actual_pa_source]
  have unit: T (burnolMobiusSourceL2 (unitPa c))=sourceVolterraWindow (barC c) (shellSource c):=by
    exact (sourceVolterraWindow_original_pa (barC c) (volterraPhysicalShell (barC c) 4)
      (volterraPhysicalShell_mem _ _)).symm
  have next:tateSource c (j+1)=sourceVolterraResolvent (barC c) (tateSource c j):=by
    rw [actual_tate_outgoing,actual_tate_outgoing,pow_succ',mul_apply_eq_comp]
  rw [map_add,map_add,map_smul,map_smul,actual_pa_source,corrected,unit,next]
  have generated:=congrArg (sourceVolterraWindow (barC c)) (actual_residual_shell_source c j)
  simp only [residualSource,map_sub,map_smul] at generated
  rw [window_cut] at generated
  linear_combination (norm:=module) generated

/-- The original external log bank is paid into the actual next Pa, rather than left as a scalar readout. -/
theorem actual_next_pa_log_bank (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    actualPa c (j+1)=
      burnolPaSourceCorrection (barC c) ⟨actualPa c j,actual_pa_mem c j⟩+
        (((-2:ℂ)^(j+1)/(j.factorial:ℂ))*
          (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^j*nativeReturn c x)) • unitPa c:=by
  rw [actual_next_pa,forcingCoefficient,actual_native_tail_log_bank]
  congr 2
  rw [pow_succ]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
