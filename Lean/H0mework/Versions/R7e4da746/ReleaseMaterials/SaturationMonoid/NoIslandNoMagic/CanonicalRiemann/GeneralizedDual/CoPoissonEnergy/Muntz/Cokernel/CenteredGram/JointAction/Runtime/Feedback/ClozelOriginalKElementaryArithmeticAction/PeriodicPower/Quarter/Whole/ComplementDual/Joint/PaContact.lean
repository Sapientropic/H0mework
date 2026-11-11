import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCollar
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaContact
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusContact
open scoped Topology
open private outgoing_power_compact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open private window_cut from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
open private fixed_admitted fixed_nonnegative from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCollar
local notation "q"=>(1/4:ℝ)
local notation "T"=>burnolTateReciprocalL2
local notation "A"=>sourceAnnulusCut
local notation "E"=>burnolQuarterZeroExtension
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "h₀"=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCollar.fixedShift
local notation "r₀"=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail.fixedRadius

/-- The actual Pa source is the complete next source cut with its one original shell debit. -/
theorem actual_pa_source_split (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    T (burnolMobiusSourceL2 (actualPa c j))=
      A (tateSource c (j+1))-forcingCoefficient c j • shellSource c:=by
  have rank:=actual_residual_shell_source c j
  simp only [residualSource,map_sub] at rank
  rw [window_cut,←actual_pa_source] at rank
  have step:tateSource c (j+1)=sourceVolterraResolvent (barC c) (tateSource c j):=by
    rw [actual_tate_outgoing,actual_tate_outgoing,pow_succ',mul_apply_eq_comp]
  rw [step]
  linear_combination (norm:=module) -rank

private theorem shell_tail (c:BurnolCompletedMellinCoordinate) (r:ℝ) (inside:r∈Icc q 4):
    burnolRadiusMellinTailEvaluator r (by linarith [inside.1]) (barC c).value (barC c).rightHalf
      (shellSource c)=(Real.log (4/r):ℂ):=by
  have positive:0<r:=by linarith [inside.1]
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  calc
    _=∫x:ℝ in Ioi r,(Iio (4:ℝ)).indicator (fun x:ℝ=>(x:ℂ)⁻¹) x:=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (volterraPhysicalShell_tate_source_raw (barC c) 4 (by norm_num)),
        ae_restrict_mem measurableSet_Ioi] with x raw beyond
      change r<x at beyond
      have positiveX:0<x:=lt_trans positive beyond
      change (x:ℂ)^(-(barC c).value)*shellSource c x=_
      rw [shellSource,raw,abs_of_pos positiveX]
      by_cases before:x<4
      · rw [if_pos (show x∈Ico q 4 from ⟨(lt_of_le_of_lt inside.1 beyond).le,before⟩),
          indicator_of_mem (show x∈Iio (4:ℝ) from before),
          ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positiveX.ne'),
          show -(barC c).value+((barC c).value-1)=(-1:ℂ) by ring,Complex.cpow_neg_one]
      · rw [if_neg (show x∉Ico q 4 from fun h=>before h.2),
          indicator_of_notMem (show x∉Iio (4:ℝ) from before),mul_zero]
    _=∫x:ℝ in Ioc r 4,(x:ℂ)⁻¹:=by
      rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
        inter_comm,Ioi_inter_Iio,←integral_Ioc_eq_integral_Ioo]
    _=_:=by
      rw [←intervalIntegral.integral_of_le inside.2]
      simp_rw [←Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal,integral_inv_of_pos positive (by norm_num)]

private theorem native_tail (c:BurnolCompletedMellinCoordinate) (j:ℕ) (r:ℝ) (lower:q≤r):
    burnolRadiusMellinTailEvaluator r (by linarith) (barC c).value (barC c).rightHalf (tateSource c j)=
      burnolRadiusMellinTailEvaluator r (by linarith) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)):=by
  have compact:=outgoing_power_compact (barC c) (nativeCompact c) j
  have zero:=source_tail_cutoff_outside (barC c) r (by linarith) q lower
    (((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c)))
  change burnolRadiusMellinTailEvaluator r _ _ _
    (FiniteMobiusResolventFlux.cutoff q (((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c))))=0 at zero
  rw [compact] at zero
  rw [actual_tate_outgoing,actual_native_source,map_add,map_add,zero,zero_add]

/-- Each Pa contact retains the next complete native tail, the full outer tail and the resonant shell logarithm. -/
theorem actual_pa_contact (c:BurnolCompletedMellinCoordinate) (j:ℕ) (r:ℝ) (inside:r∈Icc q 4):
    burnolRadiusMellinTailEvaluator r (by linarith [inside.1]) (barC c).value (barC c).rightHalf
      (T (burnolMobiusSourceL2 (actualPa c j)))=
      burnolRadiusMellinTailEvaluator r (by linarith [inside.1]) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      forcingCoefficient c j*(Real.log (4/r):ℂ):=by
  rw [actual_pa_source_split,map_sub,map_smul,shell_tail c r inside,sourceAnnulusCut_apply,map_sub,
    source_tail_cutoff_inside (barC c) r (by linarith [inside.1]) 4 inside.2,
    source_tail_cutoff_outside (barC c) r (by linarith [inside.1]) q inside.1,sub_zero,
    native_tail c (j+1) r inside.1,native_tail c (j+1) 4 (by norm_num)]
  rfl

def lowerCoefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  2*(burnolRadiusMellinTailEvaluator q (by norm_num) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      forcingCoefficient c j*(Real.log 16:ℂ))

def movingCoefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):ℂ:=
  2*(burnolRadiusMellinTailEvaluator r₀ OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail.fixed_radius_positive
        (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c))-
      forcingCoefficient c j*(h₀:ℂ))

theorem actual_lower_coefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolPaResolventSourceCoefficient (barC c) (actualPa c j)=lowerCoefficient c j:=by
  rw [←original_source_mass_eq_coefficient (barC c) (actualPa c j) (actual_pa_mem c j),
    original_source_tail_four _ _ (actual_pa_mem c j),sub_zero,actual_pa_contact c j q (by norm_num)]
  norm_num [lowerCoefficient]

theorem actual_moving_coefficient (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    sourceOuterCollarCoefficient (barC c) h₀
      (T (burnolMobiusSourceL2 (actualPa c j)))=movingCoefficient c j:=by
  have inside:r₀∈Icc q 4:=fixed_admitted
  have logarithm:Real.log (4/r₀)=h₀:=by
    have ratio:4/r₀=Real.exp h₀:=by
      rw [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail.fixedRadius,Real.exp_neg]
      field_simp
      rfl
    rw [ratio,Real.log_exp]
  simp only [sourceOuterCollarCoefficient,smul_apply,sub_apply,smul_eq_mul]
  rw [original_source_tail_four _ _ (actual_pa_mem c j),sub_zero]
  change 2*burnolRadiusMellinTailEvaluator r₀
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail.fixed_radius_positive (barC c).value (barC c).rightHalf
      (T (burnolMobiusSourceL2 (actualPa c j)))=movingCoefficient c j
  rw [actual_pa_contact c j r₀ inside,logarithm]
  rfl

/-- The original two moving collars now consume these generated native contact stocks on the actual Pa stream. -/
theorem actual_moving_contact_commutator (c:BurnolCompletedMellinCoordinate) (j:ℕ)
    (t:ℝ) (inside:t∈Ico q 4):
    finiteSourceContact (barC c) t (lt_of_lt_of_le (by norm_num) inside.1)
        (originalPhysicalCutoff 4 (burnolMultiplicativeDilation (-h₀)
          (T (burnolMobiusSourceL2 (actualPa c j))))) -
      (Real.exp (-h₀/2):ℂ)*firstContactRead (barC c) (t*Real.exp (-h₀)) (actualPa c j)=
      fullMellinTranslationCharacter (barC c).value h₀*(t:ℂ)^((barC c).value-1)*
        (movingCoefficient c j-if t*Real.exp (-h₀)<q then lowerCoefficient c j else 0):=by
  have actual:=original_source_contact_reverse_commutator (barC c) h₀ fixed_nonnegative
    (actualPa c j) (actual_pa_mem c j) t inside
  rwa [actual_moving_coefficient,actual_lower_coefficient] at actual

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
