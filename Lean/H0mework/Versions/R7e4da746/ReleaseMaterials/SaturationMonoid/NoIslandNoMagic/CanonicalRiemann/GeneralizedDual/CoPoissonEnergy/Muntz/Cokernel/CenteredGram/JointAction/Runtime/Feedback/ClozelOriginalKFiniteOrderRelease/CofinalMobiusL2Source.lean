import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.CompleteRemainder
import H0mework.Arithmetic.RemainderSource.Divisor

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.CofinalMobiusL2Source
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
namespace CM
export CofinalCanonicalSourceMaterial
 (rawIterate actualIterate iterate_raw_read iterate_raw_native raw_iterate_mean_update raw_iterate_gap actual_iterate_even
  iterate_inverse_R_action seedRaw sourceIndex canonicalRaw actual_raw_field actual_raw_source canonical_source_gap canonical_source_mean_ne)
end CM
local notation "q" => (1/4:ℝ)
local instance completePhysical : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The actual non-Schwartz Tate box, retaining the half-open endpoints of the original source. -/
def seedSource : BurnolL2 :=
 (2:ℂ) • burnolTateReciprocalL2 (burnolReciprocalStepSourceL2 1 (3/2) (by norm_num) (by norm_num))

def seedSourceRaw (t:ℝ) : ℂ := 2*burnolTateStepBoxRaw 1 (3/2) t

theorem seed_source_read : (seedSource:ℝ → ℂ)=ᵐ[volume]seedSourceRaw := by
 filter_upwards [Lp.coeFn_smul (2:ℂ)
  (burnolTateReciprocalL2 (burnolReciprocalStepSourceL2 1 (3/2) (by norm_num) (by norm_num))),
  burnolReciprocalStepSource_tate_raw 1 (3/2) (by norm_num) (by norm_num)] with t scalar actual
 change seedSource t=_ at scalar
 rw [scalar,Pi.smul_apply,smul_eq_mul,actual]
 rfl

theorem seed_source_gap {t:ℝ} (inside:|t|<1) : seedSourceRaw t=0 := by
 unfold seedSourceRaw burnolTateStepBoxRaw
 rw [if_neg (by rintro ⟨lower,_⟩;exact not_le_of_gt inside lower),mul_zero]

private theorem seed_source_quarter : ∀{t:ℝ},|t|≤q → seedSourceRaw t=0 := by
 intro t inside
 exact seed_source_gap (by linarith)

private theorem seed_source_even (t:ℝ) : seedSourceRaw (-t)=seedSourceRaw t := by
 simp only [seedSourceRaw,burnolTateStepBoxRaw,abs_neg]

private theorem seed_source_zero : seedSourceRaw 0=0 := seed_source_gap (by norm_num)

private theorem seed_source_forward (t:ℝ) :
 burnolInnerGapForward seedSourceRaw t=
   2*(∑ n∈burnolHarmonicStepChannels 1 (3/2) t,(n:ℂ)⁻¹) := by
 calc
  _=∑' n:ℕ+,(2:ℂ)*((((n:ℕ):ℂ)⁻¹)*burnolTateStepBoxRaw 1 (3/2) (t/(n:ℕ))) := by
   apply tsum_congr
   intro n
   unfold seedSourceRaw
   ring
  _=2*burnolInnerGapForward (burnolTateStepBoxRaw 1 (3/2)) t := by
   rw [tsum_mul_left]
   rfl
  _=_ := by rw [burnolTateStepBox_finiteCoSum 1 (3/2) t (by norm_num) (by norm_num)]

private theorem seed_value_forward :
 CM.seedRaw=(fun t => burnolInnerGapForward seedSourceRaw t-2*(Real.log (3/2:ℝ):ℂ)) := by
 funext t
 rw [seed_source_forward]
 unfold CofinalCanonicalSourceMaterial.seedRaw burnolHarmonicStepWaveRaw
 rw [div_one]
 ring

/-- Existing generic divisor inversion recovers the actual box without a Schwartz constructor. -/
theorem seed_inverse_source (t:ℝ) : burnolCenteredMobiusInverse CM.seedRaw t=seedSourceRaw t := by
 rw [seed_value_forward]
 exact burnolCenteredMobiusInverse_forward_innerGap seedSourceRaw seed_source_quarter _ t

private theorem seed_value_gap : ∀{t:ℝ},|t|≤q → CM.seedRaw t=CM.seedRaw 0 := by
 intro t inside
 rw [seed_value_forward]
 change burnolInnerGapForward seedSourceRaw t-_=burnolInnerGapForward seedSourceRaw 0-_
 rw [burnolInnerGapForward_innerGap seedSourceRaw seed_source_quarter inside,
  burnolInnerGapForward_innerGap seedSourceRaw seed_source_quarter (by norm_num)]

private theorem seed_value_read :
 ((burnolPaCombApproximation 0:BurnolL2):ℝ → ℂ)=ᵐ[volume]CM.seedRaw := by
 convert burnolPaCombApproximation_coeFn 0 using 1
 norm_num [burnolPaCombSourceWidth]
 rfl

private theorem seed_value_even : reflectL2 (burnolPaCombApproximation 0:BurnolL2)=(burnolPaCombApproximation 0:BurnolL2) :=
 mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2

private theorem seed_source_even_l2 : reflectL2 seedSource=seedSource :=
 burnolReflectL2_eq_of_even_raw seedSource seedSourceRaw seed_source_read seed_source_even

def sourceField (c:BurnolCompletedMellinCoordinate) (j:Nat) : BurnolL2 := CM.actualIterate c seedSource j

def sourceRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) : ℝ → ℂ := CM.rawIterate c seedSourceRaw j

def valueField (c:BurnolCompletedMellinCoordinate) (j:Nat) : BurnolL2 :=
 CM.actualIterate c (burnolPaCombApproximation 0:BurnolL2) j

def valueRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) : ℝ → ℂ := CM.rawIterate c CM.seedRaw j

theorem source_raw_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 (sourceField c j:ℝ → ℂ)=ᵐ[volume]sourceRaw c j :=
 CM.iterate_raw_read c seedSource seedSourceRaw seed_source_read
  (fun inside => (seed_source_quarter inside).trans seed_source_zero.symm) seed_source_even_l2 j

theorem value_raw_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 (valueField c j:ℝ → ℂ)=ᵐ[volume]valueRaw c j :=
 CM.iterate_raw_read c _ CM.seedRaw seed_value_read seed_value_gap seed_value_even j

theorem source_raw_zero (c:BurnolCompletedMellinCoordinate) (j:Nat) : sourceRaw c j 0=0 := by
 induction j with
 | zero => exact seed_source_zero
 | succ j previous =>
  change CM.rawIterate c seedSourceRaw (j+1) 0=0
  change CM.rawIterate c seedSourceRaw j 0=0 at previous
  rw [CM.raw_iterate_mean_update,previous,mul_zero,zero_div]

theorem source_raw_gap (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 ∀{t:ℝ},|t|<1 → sourceRaw c j t=0 := by
 induction j with
 | zero => exact seed_source_gap
 | succ j previous =>
  intro t inside
  have integralZero:(∫ v:ℝ in 0..|t|,OriginalKCenteredMobiusRSource.weightedCentered c (sourceRaw c j) v)=0 := by
   rw [intervalIntegral.integral_of_le (abs_nonneg t)]
   apply setIntegral_eq_zero_of_forall_eq_zero
   intro v bounds
   have small:|v|<1:=by rw [abs_of_nonneg bounds.1.le];exact bounds.2.trans_lt inside
   unfold OriginalKCenteredMobiusRSource.weightedCentered
   rw [previous small,source_raw_zero,sub_self,mul_zero]
  change OriginalKCenteredMobiusRSource.sourceRRaw c (sourceRaw c j) t=0
  rw [OriginalKCenteredMobiusRSource.sourceRRaw,source_raw_zero,integralZero]
  simp only [mul_zero,zero_div,sub_zero]

theorem source_native (c:BurnolCompletedMellinCoordinate) (j:Nat) : MemLp (sourceRaw c j) 2 volume :=
 (memLp_congr_ae (source_raw_read c j)).mp (Lp.memLp _)

theorem source_action (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 burnolDirectRightResolvent ((c).value/2) (sourceField c j)=sourceField c (j+1) := rfl

private theorem raw_iterate_even (c:BurnolCompletedMellinCoordinate) (raw:ℝ → ℂ)
 (initial:∀t:ℝ,raw (-t)=raw t) (j:Nat) (t:ℝ) : CM.rawIterate c raw j (-t)=CM.rawIterate c raw j t := by
 cases j with
 | zero => exact initial t
 | succ j => simp only [CM.rawIterate,OriginalKCenteredMobiusRSource.sourceRRaw,abs_neg]

private theorem inverse_even (raw:ℝ → ℂ) (even:∀t:ℝ,raw (-t)=raw t) (t:ℝ) :
 burnolCenteredMobiusInverse raw (-t)=burnolCenteredMobiusInverse raw t := by
 unfold burnolCenteredMobiusInverse
 apply tsum_congr
 intro n
 rw [neg_div,even]

theorem native_inverse_source (c:BurnolCompletedMellinCoordinate) (j:Nat) (t:ℝ) :
 burnolCenteredMobiusInverse (valueRaw c j) t=sourceRaw c j t := by
 induction j generalizing t with
 | zero => exact seed_inverse_source t
 | succ j previous =>
  have positiveStep:∀x:ℝ,0<x → burnolCenteredMobiusInverse (valueRaw c (j+1)) x=sourceRaw c (j+1) x := by
   intro x positive
   have action:=CM.iterate_inverse_R_action c (burnolPaCombApproximation 0:BurnolL2) CM.seedRaw
    seed_value_read seed_value_gap seed_value_even j x positive
   change burnolCenteredMobiusInverse (valueRaw c (j+1)) x=_ at action
   rw [action]
   have same:(∫ v:ℝ in 0..x,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse (valueRaw c j) v)=
     ∫ v:ℝ in 0..x,(v:ℂ)^((c).value-1)*sourceRaw c j v := by
      apply intervalIntegral.integral_congr
      intro v _
      change (v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse (valueRaw c j) v=_
      rw [previous]
   change -2*(x:ℂ)^(-(c).value)*(∫ v:ℝ in 0..x,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse (valueRaw c j) v)=_
   rw [same]
   change _=OriginalKCenteredMobiusRSource.sourceRRaw c (sourceRaw c j) x
   simp only [OriginalKCenteredMobiusRSource.sourceRRaw,source_raw_zero,mul_zero,zero_div,
    abs_of_pos positive,OriginalKCenteredMobiusRSource.weightedCentered,sub_zero,zero_sub]
   ring
  by_cases positive:0<t
  · exact positiveStep t positive
  · by_cases zero:t=0
    · subst t
      simp only [burnolCenteredMobiusInverse,zero_div,sub_self,mul_zero,tsum_zero,source_raw_zero]
    · have negative:t<0:=lt_of_le_of_ne (le_of_not_gt positive) zero
      have rawEven:∀x:ℝ,valueRaw c (j+1) (-x)=valueRaw c (j+1) x :=
       raw_iterate_even c CM.seedRaw (fun x => by simp only [CofinalCanonicalSourceMaterial.seedRaw,burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,abs_neg]) (j+1)
      calc
       _=burnolCenteredMobiusInverse (valueRaw c (j+1)) (-t) := (inverse_even _ rawEven t).symm
       _=sourceRaw c (j+1) (-t) := positiveStep (-t) (by linarith)
       _=sourceRaw c (j+1) t := raw_iterate_even c seedSourceRaw seed_source_even (j+1) t

theorem native_inverse_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 (fun t => burnolCenteredMobiusInverse (valueRaw c j) t)=ᵐ[volume](sourceField c j:ℝ → ℂ) := by
 have actual:(fun t => burnolCenteredMobiusInverse (valueRaw c j) t)=ᵐ[volume]sourceRaw c j :=
  Filter.Eventually.of_forall (native_inverse_source c j)
 exact actual.trans (source_raw_read c j).symm

theorem native_inverse_memLp (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 MemLp (fun t => burnolCenteredMobiusInverse (valueRaw c j) t) 2 volume :=
 (memLp_congr_ae (native_inverse_read c j)).mpr (Lp.memLp _)

private theorem original_seed_value : (burnolPaCombApproximation 0:BurnolL2)=
 (2:ℂ) • fourierL2 (burnolReciprocalStepWaveL2 1 (3/2) (by norm_num) (by norm_num)) := by
 have actual:=burnolPaCombApproximation_raw 0
 norm_num [burnolPaCombSourceWidth] at actual
 rw [burnolReciprocalStepNativeWave_eq 1 (3/2) (by norm_num) (by norm_num)] at actual
 exact actual

private theorem seed_realizes (test:SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead seedSource test=
 (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolPaCombApproximation 0:BurnolL2)) test := by
 have actual:=burnolRemainderRealization_fourier
  (burnolReciprocalStepSourceL2 1 (3/2) (by norm_num) (by norm_num))
  (burnolReciprocalStepWaveL2 1 (3/2) (by norm_num) (by norm_num))
  (burnolReciprocalStepSource_realizes 1 (3/2) (by norm_num) (by norm_num) (by norm_num)) test
 change burnolRemainderSourceRead ((2:ℂ) • _ ) test=_
 rw [←burnolRemainderSourceReadCLM_apply,map_smul,burnolRemainderSourceReadCLM_apply,actual,original_seed_value]
 simp only [map_smul,smul_apply]

/-- Consume the existing full R Bochner/dilation square on the actual source and value together. -/
private theorem resolvent_realizes (c:BurnolCompletedMellinCoordinate) (source value:BurnolL2)
 (realizes:∀test:SchwartzMap ℝ ℂ,burnolRemainderSourceRead source test=
   (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) (test:SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (burnolDirectRightResolvent ((c).value/2) source) test=
 (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolDirectRightResolvent ((c).value/2) value)) test := by
 have right:1/4<((c).value/2).re:=by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
 have integrated:=burnolRemainderSourceRead_bochner (volume.restrict (Ioi (0:ℝ)))
  (burnolDirectRightResolventIntegrand ((c).value/2) source) (burnolDirectRightResolventIntegrand ((c).value/2) value)
  (burnolDirectRightResolventIntegrand_integrableOn _ right source)
  (burnolDirectRightResolventIntegrand_integrableOn _ right value) (by
   filter_upwards with h test
   unfold burnolDirectRightResolventIntegrand
   rw [←burnolRemainderSourceReadCLM_apply,map_smul,burnolRemainderSourceReadCLM_apply,
    burnolRemainderRealization_dilation source value realizes]
   simp only [map_smul,smul_apply]) test
 unfold burnolDirectRightResolvent
 rw [←burnolRemainderSourceReadCLM_apply,map_neg,burnolRemainderSourceReadCLM_apply,integrated]
 simp only [map_neg,neg_apply]

theorem source_realizes (c:BurnolCompletedMellinCoordinate) (j:Nat) (test:SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (sourceField c j) test=
 (Lp.toTemperedDistributionCLM ℂ volume 2 (valueField c j)) test := by
 induction j generalizing test with
 | zero => exact seed_realizes test
 | succ j previous => exact resolvent_realizes c (sourceField c j) (valueField c j) previous test

theorem source_realizes_integral (c:BurnolCompletedMellinCoordinate) (j:Nat) (test:SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (sourceField c j) test=∫ t:ℝ,test t*valueField c j t := by
 simpa only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using source_realizes c j test

private theorem actual_quarter_constant_read {gamma delta:ℂ}
 (same:∀ᵐ _x:ℝ ∂volume.restrict (Icc (-q) q),gamma=delta) : gamma=delta := by
 obtain ⟨x,inside,read⟩:=Measure.exists_mem_of_measure_ne_zero_of_ae
  (μ:=(volume:Measure ℝ)) (s:=Icc (-q) q) (by norm_num [Real.volume_Icc]) same
 exact read

def reciprocalMoment (c:BurnolCompletedMellinCoordinate) (j:Nat) : ℂ :=
 ∫ u:ℝ in Ioi 0,(u:ℂ)⁻¹*sourceRaw c j u

/-- The full actual realization and its literal source gap generate the reciprocal moment, never assume it. -/
theorem source_reciprocal_moment (c:BurnolCompletedMellinCoordinate) (j:Nat) :
 reciprocalMoment c j= -valueRaw c j 0 := by
 have even:reflectL2 (sourceField c j)=sourceField c j:=
  CM.actual_iterate_even c seedSource seed_source_even_l2 j
 have quarter:∀{x:ℝ},|x|≤q → sourceRaw c j x=0:=by
  intro x inside
  exact source_raw_gap c j (by linarith)
 have gap:(sourceField c j:ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)]fun _ => 0 := by
  filter_upwards [ae_restrict_of_ae (source_raw_read c j),ae_restrict_mem (measurableSet_symmetricInterval q)]
   with x actual inside
  rw [actual,quarter (abs_le.mpr inside)]
 obtain ⟨rep,repRead,repGap,valueRead⟩:=burnolRemainderSourceRead_realization_ae
  (sourceField c j) (valueField c j) even gap (source_realizes_integral c j)
 have same:rep=ᵐ[volume]sourceRaw c j:=repRead.symm.trans (source_raw_read c j)
 have forward:=burnolInnerGapForward_ae_congr rep (sourceRaw c j) same
 have moment:(∫ u:ℝ in Ioi 0,(u:ℂ)⁻¹*rep u)=reciprocalMoment c j := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae same] with u actual
  rw [actual]
 have full:valueRaw c j=ᵐ[volume](fun x => burnolInnerGapForward (sourceRaw c j) x-reciprocalMoment c j) := by
  apply (value_raw_read c j).symm.trans
  apply valueRead.trans
  filter_upwards [forward] with x actual
  rw [actual,moment]
 have constants:∀ᵐ _x:ℝ ∂volume.restrict (Icc (-q) q),valueRaw c j 0= -reciprocalMoment c j := by
  filter_upwards [ae_restrict_of_ae full,ae_restrict_mem measurableSet_Icc] with x actual inside
  have small:|x|≤q:=abs_le.mpr inside
  change CM.rawIterate c CM.seedRaw j x=_ at actual
  rw [CM.raw_iterate_gap c CM.seedRaw seed_value_gap j small,
   burnolInnerGapForward_innerGap (sourceRaw c j) quarter small,zero_sub] at actual
  exact actual
 have generated:=actual_quarter_constant_read constants
 simpa only [neg_neg] using (congrArg Neg.neg generated).symm

/-- Endpoint controls keep the actual half-open compact seed, including the nonzero left endpoint. -/
theorem seed_endpoint_inventory :
 seedSourceRaw 0=0 ∧ seedSourceRaw 1=2 ∧ seedSourceRaw (3/2)=0 ∧
 (∀t:ℝ,(3/2:ℝ)≤|t| → seedSourceRaw t=0) := by
 refine ⟨seed_source_zero,by norm_num [seedSourceRaw,burnolTateStepBoxRaw],
  by norm_num [seedSourceRaw,burnolTateStepBoxRaw],?_⟩
 intro t outside
 unfold seedSourceRaw burnolTateStepBoxRaw
 rw [if_neg (by rintro ⟨_,upper⟩;exact not_lt_of_ge outside upper),mul_zero]

end OriginalKFiniteOrderRelease.CofinalMobiusL2Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
