import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterClock
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterShell
open scoped InnerProductSpace Topology
open private tateTail_read from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.DyadicSource
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "ν" => burnolMobiusSourceL2

def quarterShellSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolRadiusNormalizedUnitTail coordinate q (by norm_num)-burnolNormalizedFirstSourceUnitTail coordinate

def quarterShellRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if q < |x| ∧ |x|≤4 then -((|x| : ℝ) : ℂ)^(-coordinate.value) else 0

theorem actual_quarter_shell_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (quarterShellSource coordinate : ℝ → ℂ)=ᵐ[volume] quarterShellRaw coordinate := by
  filter_upwards [Lp.coeFn_sub (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))
    (burnolNormalizedFirstSourceUnitTail coordinate),burnolRadiusUnitTail_coeFn coordinate q (by norm_num),
    burnolNormalizedFirstSourceUnitTail_coeFn coordinate] with x difference lower upper
  rw [quarterShellSource,difference,Pi.sub_apply,lower,upper]
  unfold burnolNormalizedFirstSourceUnitTailRaw
  unfold quarterShellRaw
  by_cases below : q < |x|
  · by_cases above : 4 < |x|
    · rw [if_pos below,if_pos above,sub_self,if_neg (fun active => not_lt_of_ge active.2 above)]
    · rw [if_pos below,if_neg above,sub_zero,if_pos ⟨below,le_of_not_gt above⟩]
  · have notAbove : ¬4 < |x| := by linarith
    rw [if_neg below,if_neg notAbove,sub_self,if_neg (fun active => below active.1)]

/-- Faithful inversion recovers the actual finite q..4 source, including both original endpoints. -/
theorem actual_quarter_shell_inverse (coordinate : BurnolCompletedMellinCoordinate) :
    ν (quarterShellPa coordinate)=quarterShellSource coordinate := by
  have raw := actual_quarter_shell_raw coordinate
  have even : reflectL2 (quarterShellSource coordinate)=quarterShellSource coordinate :=
    burnolReflectL2_eq_of_even_raw _ _ raw (fun x => by simp only [quarterShellRaw,abs_neg])
  have gap : (quarterShellSource coordinate : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae raw,ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    rw [read,quarterShellRaw,if_neg (fun active => (not_lt_of_ge (abs_le.mpr inside)) active.1)]
  have realizes (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead (quarterShellSource coordinate) test=
      ∫ x : ℝ,test x*(quarterShellPa coordinate : BurnolL2) x := by
    simpa only [quarterShellSource,quarterShellPa,Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply,smul_eq_mul] using actual_quarter_shell_realizes coordinate test
  rw [burnolRemainderSourceRead_cutoff_source _ _ even gap realizes]
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction 4 (quarterShellSource coordinate)),
    (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) (quarterShellSource coordinate)),raw]
    with x extended restricted read
  rw [extended]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside]
    exact restricted inside
  · rw [indicator_of_notMem inside,read,quarterShellRaw,
      if_neg (fun active => inside (abs_le.mp active.2))]

theorem actual_quarter_shell_tate_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (T (ν (quarterShellPa coordinate)) : ℝ → ℂ)=ᵐ[volume] fun x =>
      (if |x|<4 then -((|x| : ℝ) : ℂ)^(coordinate.value-1) else 0)-
        (if |x|<q then -((|x| : ℝ) : ℂ)^(coordinate.value-1) else 0) := by
  rw [actual_quarter_shell_inverse,quarterShellSource,map_sub]
  have lower := tateTail_read coordinate q (by norm_num)
  have upper := tateTail_read coordinate 4 (by norm_num)
  norm_num only [show (q : ℝ)⁻¹=4 by norm_num] at lower
  norm_num only [show (4 : ℝ)⁻¹=q by norm_num] at upper
  filter_upwards [Lp.coeFn_sub
    (T (burnolRadiusNormalizedUnitTail coordinate q (by norm_num)))
    (T (burnolNormalizedFirstSourceUnitTail coordinate)),lower,upper] with x difference low high
  exact difference.trans (congrArg₂ (·-·) low high)

/-- The resonant shell contact is its complete logarithmic clock, generated from the inverse source. -/
theorem actual_quarter_shell_coefficient (coordinate : BurnolCompletedMellinCoordinate) :
    burnolPaResolventSourceCoefficient coordinate (quarterShellPa coordinate)=-(2 : ℂ)*(Real.log 16 : ℂ) := by
  change 2*burnolMellinTailEvaluator coordinate.value coordinate.rightHalf (T (ν (quarterShellPa coordinate)))=_
  rw [burnolMellinTailEvaluator_eq_integral]
  have source : (∫ x : ℝ in Ioi q,(x : ℂ)^(-coordinate.value)*T (ν (quarterShellPa coordinate)) x)=
      -(Real.log 16 : ℂ) := by
    calc
      _=∫ x : ℝ in Ioi q,(Iio (4 : ℝ)).indicator (fun x : ℝ => -(x : ℂ)⁻¹) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (actual_quarter_shell_tate_raw coordinate),
          ae_restrict_mem measurableSet_Ioi] with x raw beyond
        change q<x at beyond
        have positive : 0<x := lt_trans (by norm_num : (0 : ℝ)<q) beyond
        rw [raw,abs_of_pos positive,if_neg (not_lt_of_ge beyond.le),sub_zero]
        by_cases before : x<4
        · rw [if_pos before,indicator_of_mem (show x∈Iio (4 : ℝ) from before),mul_neg,
            ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
            show -coordinate.value+(coordinate.value-1)=(-1 : ℂ) by ring,Complex.cpow_neg_one]
        · rw [if_neg before,mul_zero,indicator_of_notMem (show x∉Iio (4 : ℝ) from before)]
      _=∫ x : ℝ in Ioc q 4,-(x : ℂ)⁻¹ := by
        rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
          inter_comm,Ioi_inter_Iio,←integral_Ioc_eq_integral_Ioo]
      _=_ := by
        rw [←intervalIntegral.integral_of_le (by norm_num : q≤(4 : ℝ)),intervalIntegral.integral_neg]
        simp_rw [←Complex.ofReal_inv]
        rw [intervalIntegral.integral_ofReal,integral_inv_of_pos (by norm_num : (0 : ℝ)<q) (by norm_num)]
        norm_num
  change 2*(∫ x : ℝ in Ioi q,(x : ℂ)^(-coordinate.value)*T (ν (quarterShellPa coordinate)) x)=_
  rw [source]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : ℕ,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
include nontrivial
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource

/-- The original m consumer receives the computed clock instead of an opaque shell coefficient. -/
theorem actual_quarter_original_top_clock :
    inner ℂ (sourceKernelCombo c) (quarterUnitPower c m)=
      inner ℂ (sourceKernelCombo c) (unitPower observation half m)-
        (2 : ℂ)*(Real.log 16 : ℂ)*feedbackCoefficient observation half := by
  rw [actual_quarter_combo_top observation nontrivial half,actual_quarter_shell_coefficient]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
