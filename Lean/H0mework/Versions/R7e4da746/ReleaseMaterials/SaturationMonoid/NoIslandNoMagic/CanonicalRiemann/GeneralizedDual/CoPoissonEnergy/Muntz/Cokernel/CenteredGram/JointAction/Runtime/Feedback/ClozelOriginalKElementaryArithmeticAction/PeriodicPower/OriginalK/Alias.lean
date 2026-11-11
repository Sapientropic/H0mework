import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.CompactTail
import Mathlib.Analysis.Fourier.PoissonSummation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.Alias
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
open scoped Topology InnerProductSpace FourierTransform
open private compact_tail from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.CompactTail
open private box_fourier_trig from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open private box_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

def returnCompactRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  burnolRieszReturnRaw c (min |x| q)-burnolRieszReturnRaw c q

def returnFourier (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  InverseTail.smoothFourier c x-burnolRieszReturnRaw c q*box x

theorem actual_return_compact_continuous (c:BurnolCompletedMellinCoordinate):
    Continuous (returnCompactRaw c) :=
  ((burnolRieszReturnRaw_continuous c).comp (continuous_abs.min continuous_const)).sub
    continuous_const

theorem actual_return_compact_raw (c:BurnolCompletedMellinCoordinate):
    returnCompactRaw c=(symmetricInterval q).indicator
      (fun x=>burnolRieszReturnRaw c x-burnolRieszReturnRaw c q) := by
  funext x
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,returnCompactRaw,min_eq_left (abs_le.mpr inside)]
    rcases le_or_gt 0 x with positive|negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_neg negative,return_raw_even]
  · rw [indicator_of_notMem inside,returnCompactRaw,
      min_eq_right (le_of_not_ge (fun bounded=>inside (abs_le.mp bounded)))]
    exact sub_self _

theorem actual_return_compact_support (c:BurnolCompletedMellinCoordinate):
    HasCompactSupport (returnCompactRaw c) := by
  apply HasCompactSupport.intro (K:=symmetricInterval q) isCompact_Icc
  intro x outside
  rw [actual_return_compact_raw,indicator_of_notMem outside]

private theorem return_fourier_continuous (c:BurnolCompletedMellinCoordinate):
    Continuous (returnFourier c) :=
  (Constructor.fourierRaw_continuous _ (burnolRieszReturnRaw_continuous c)).sub
    (continuous_const.mul (burnolRadiusTruncatedFourierRaw_continuous _))

private theorem return_fourier_even (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    returnFourier c (-x)=returnFourier c x := by
  have first:InverseTail.smoothFourier c (-x)=InverseTail.smoothFourier c x := by
    rw [ProlateKernel.original_return_kernel,ProlateKernel.original_return_kernel]
    apply integral_congr_ae
    filter_upwards with y
    simp only [ProlateKernel.kernel,Complex.ofReal_neg,mul_neg,neg_mul,Complex.cos_neg]
  have second:box (-x)=box x := by
    by_cases zero:x=0
    · simp [zero]
    · rw [box_fourier_trig x zero,box_fourier_trig (-x) (neg_ne_zero.mpr zero)]
      simp only [Complex.ofReal_neg,mul_neg,Complex.sin_neg,div_neg,neg_div,neg_neg]
  rw [returnFourier,returnFourier,first,second]

/-- The original return has its own q endpoint removed, before any alias is summed. -/
theorem actual_return_fourier_bound (c:BurnolCompletedMellinCoordinate):
    ∃ D:ℝ,0≤D∧∀x:ℝ,x≠0→‖returnFourier c x‖≤D/|x|^2 := by
  have smooth:ContDiff ℝ 2 (burnolRieszReturnRaw c):=
    (ProlateReturn.original_return_contDiff c).of_le
      (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))
  obtain ⟨D,nonnegative,tail⟩:=compact_tail smooth (return_raw_even c)
  obtain ⟨C,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc (-1:ℝ) 1) (return_fourier_continuous c).continuousOn
  have Cnonnegative:0≤C := (norm_nonneg _).trans (bounded 0 (by constructor <;> norm_num))
  have large (x:ℝ) (one:1≤x):‖returnFourier c x‖≤D/x^2 := by
    have source:=tail x one
    have xn:x≠0:=by linarith
    have read:ProlateTransform.transform (burnolRieszReturnRaw c) x=
        InverseTail.smoothFourier c x:=(ProlateKernel.original_return_kernel c x).symm
    rw [read] at source
    convert source using 1
    rw [returnFourier,box_fourier_trig x xn]
    unfold ProlateKernel.frequency
    ring
  refine ⟨D+C,add_nonneg nonnegative Cnonnegative,fun x xn=>?_⟩
  have xpos:0 < |x| :=abs_pos.mpr xn
  by_cases one:1≤|x|
  · have source:=large |x| one
    have same:returnFourier c |x|=returnFourier c x := by
      rcases le_or_gt 0 x with p|n
      · rw [abs_of_nonneg p]
      · rw [abs_of_neg n,return_fourier_even]
    rw [same] at source
    exact source.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right Cnonnegative) (sq_nonneg _))
  · have small:|x|≤1:=le_of_not_ge one
    have source:=bounded x (abs_le.mp small)
    apply (le_div_iff₀ (sq_pos_of_pos xpos)).mpr
    have square:|x|^2≤1:=by nlinarith [sq_nonneg (|x|-1)]
    nlinarith [mul_le_mul_of_nonneg_right source (sq_nonneg |x|),
      mul_le_mul_of_nonneg_left square Cnonnegative]

theorem actual_return_fourier (c:BurnolCompletedMellinCoordinate):
    𝓕 (returnCompactRaw c)=returnFourier c := by
  have first (x:ℝ):𝓕 (returnCompactRaw c) x=
      Constructor.fourierRaw (fun y=>burnolRieszReturnRaw c y-burnolRieszReturnRaw c q) x := by
    rw [Real.fourier_eq,actual_return_compact_raw]
    unfold Constructor.fourierRaw VectorFourier.fourierIntegral
    rw [←integral_indicator (measurableSet_symmetricInterval q)]
    apply integral_congr_ae
    filter_upwards with y
    by_cases inside:y∈symmetricInterval q
    · rw [indicator_of_mem inside,indicator_of_mem inside]
      simp only [innerₗ_apply_apply]
    · rw [indicator_of_notMem inside,indicator_of_notMem inside,smul_zero]
  funext x
  rw [first,returnFourier,InverseTail.smoothFourier,box_read]
  simp_rw [Constructor.fourierRaw_integral]
  have one:IntervalIntegrable (fun y=>Constructor.phase x y*burnolRieszReturnRaw c y) volume (-q) q:=
    ((Constructor.phaseContinuous x).mul (burnolRieszReturnRaw_continuous c)).intervalIntegrable (-q) q
  have two:IntervalIntegrable (fun y=>Constructor.phase x y*(1:ℂ)) volume (-q) q:=
    ((Constructor.phaseContinuous x).mul (continuous_const (y:=(1:ℂ)))).intervalIntegrable (-q) q
  rw [←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_sub one (two.const_mul (burnolRieszReturnRaw c q))]
  apply intervalIntegral.integral_congr
  intro y _
  ring

private theorem shifted_distance (x:ℝ) (inside:|x|≤q) (k:ℤ) (nonzero:k≠0):
    (1/2:ℝ)*|(k:ℝ)|≤|x+k| := by
  have one:(1:ℝ)≤|(k:ℝ)| :=by exact_mod_cast Int.one_le_abs nonzero
  have triangle:=abs_add_le (x+k) (-x)
  rw [abs_neg,show x+(k:ℝ)+ -x=(k:ℝ) by ring] at triangle
  linarith

theorem actual_return_shift_summable (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:|x|≤q):Summable (fun k:ℤ=>returnFourier c (x+k)) := by
  obtain ⟨D,nonnegative,bound⟩:=actual_return_fourier_bound c
  have major:Summable (fun k:ℤ=>4*D/(k:ℝ)^2):=by
    simpa only [div_eq_mul_inv,one_mul] using
      (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*D)
  have outer:Summable (fun k:ℤ=>if k=0 then 0 else returnFourier c (x+k)) := by
    apply Summable.of_norm_bounded major
    intro k
    by_cases zero:k=0
    · simp [zero]
    · rw [if_neg zero]
      have distance:=shifted_distance x inside k zero
      have kp:0 < |(k:ℝ)| :=abs_pos.mpr (by exact_mod_cast zero)
      have xp:0 < |x+k| :=lt_of_lt_of_le (by positivity) distance
      apply (bound (x+k) (abs_pos.mp xp)).trans
      have square:(k:ℝ)^2≤4*|x+k|^2:=by nlinarith [sq_abs (k:ℝ)]
      apply (div_le_div_iff₀ (sq_pos_of_pos xp) (sq_pos_of_ne_zero (by exact_mod_cast zero))).mpr
      nlinarith [mul_le_mul_of_nonneg_left square nonnegative]
  apply ((hasSum_ite_eq (0:ℤ) (returnFourier c x)).summable.add outer).congr
  intro k
  by_cases zero:k=0 <;> simp [zero]

/-- Modulation keeps the same compact source; the Fourier samples are shifted, not relabelled. -/
theorem actual_return_periodization (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:|x|≤q):
    ∑'k:ℤ,returnFourier c (x+k)=burnolRieszReturnRaw c 0-burnolRieszReturnRaw c q := by
  let modulated:ℝ→ℂ:=fun y=>Constructor.phase x y*returnCompactRaw c y
  have continuous:Continuous modulated:=
    (Constructor.phaseContinuous x).mul (actual_return_compact_continuous c)
  have compact:HasCompactSupport modulated := by
    apply HasCompactSupport.intro (K:=symmetricInterval q) isCompact_Icc
    intro y outside
    dsimp only [modulated]
    rw [actual_return_compact_raw,indicator_of_notMem outside,mul_zero]
  have decay:Asymptotics.IsBigO (cocompact ℝ) modulated (fun y:ℝ=>|y|^(-2:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have vanishes:modulated=ᶠ[cocompact ℝ]0:=by
      simpa only [coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp compact
    filter_upwards [vanishes] with y read
    simp only [read,Pi.zero_apply,norm_zero,zero_mul,le_refl]
  have fourier (k:ℝ):𝓕 modulated k=returnFourier c (x+k) := by
    rw [←actual_return_fourier]
    simp only [Real.fourier_eq,modulated,Circle.smul_def,smul_eq_mul,Real.inner_apply]
    apply integral_congr_ae
    filter_upwards with y
    rw [←mul_assoc]
    congr 1
    unfold Constructor.phase
    rw [←Circle.coe_mul,←Real.fourierChar.map_add_eq_mul]
    congr 2
    ring
  have series:Summable (fun k:ℤ=>𝓕 modulated (k:ℝ)) := by
    simpa only [fourier] using actual_return_shift_summable c x inside
  have poisson:=Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable continuous
    (b:=2) (by norm_num) decay series 0
  simp only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one,fourier] at poisson
  have samples (n:ℤ):modulated (n:ℝ)=
      if n=0 then burnolRieszReturnRaw c 0-burnolRieszReturnRaw c q else 0 := by
    by_cases zero:n=0
    · subst n
      simp [modulated,Constructor.phase,returnCompactRaw]
    · rw [if_neg zero]
      have integer:(1:ℝ)≤|(n:ℝ)| :=by exact_mod_cast Int.one_le_abs zero
      have outside:(n:ℝ)∉symmetricInterval q:=by
        intro member
        have bounded:=abs_le.mpr member
        linarith
      dsimp only [modulated]
      rw [actual_return_compact_raw,indicator_of_notMem outside,mul_zero]
  simpa only [samples,tsum_ite_eq] using poisson.symm

def kernelAliasTerm (c:BurnolCompletedMellinCoordinate) (k:ℤ) (x:ℝ):ℂ :=
  if k=0 then 0 else
    (burnolRieszFourierRaw c (x+k)-Kernel.A c*box (x+k))-
      (burnolRieszFourierRaw c k-Kernel.A c*box k)

def kernelAlias (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  ∑'k:ℤ,kernelAliasTerm c k x

private theorem actual_exterior_field (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (outside:q < |x|):
    burnolRieszFourierRaw c x-Kernel.A c*box x=
      resolvedFourierRaw c x+returnFourier c x := by
  have direct:x∉symmetricInterval q:=fun h=>not_lt_of_ge (abs_le.mpr h) outside
  have negative:-x∉symmetricInterval q:=by
    intro h
    have h':|-x|≤q:=abs_le.mpr h
    rw [abs_neg] at h'
    exact not_lt_of_ge h' outside
  have returned:burnolRadiusTruncatedFourierRaw q
      (Constructor.returnState c:BurnolQuarterIntervalL2)=InverseTail.smoothFourier c :=
    Constructor.fourierRaw_congr _ _ (Constructor.returnState_read c)
  have exterior:burnolRieszFourierExteriorRaw c x=
      ForcingWhole.raw c x+InverseTail.smoothFourier c x := by
    change ForcingWhole.raw c x+(1/2:ℂ)*
      (burnolRadiusTruncatedFourierRaw q (Constructor.returnState c:BurnolQuarterIntervalL2) x+
        burnolRadiusTruncatedFourierRaw q (Constructor.returnState c:BurnolQuarterIntervalL2) (-x))=_
    rw [OriginalRieszFinitePairing.return_fourier_even,returned]
    ring
  rw [burnolRieszFourierRaw,burnolEvenRaw,indicator_of_notMem direct,
    indicator_of_notMem negative,zero_add,mul_zero,sub_zero,exterior,actual_original_A]
  unfold resolvedFourierRaw returnFourier positionEndpoint
  ring

private def returnAliasTerm (c:BurnolCompletedMellinCoordinate) (k:ℤ) (x:ℝ):ℂ :=
  if k=0 then 0 else returnFourier c (x+k)

private theorem return_alias_summable (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:|x|≤q):Summable (fun k:ℤ=>returnAliasTerm c k x) := by
  apply ((actual_return_shift_summable c x inside).sub
    (hasSum_ite_eq (0:ℤ) (returnFourier c x)).summable).congr
  intro k
  by_cases zero:k=0 <;> simp [zero,returnAliasTerm]

private theorem resolved_alias_summable (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:|x|≤q):Summable (fun k:ℤ=>aliasRawTerm c k x) := by
  have major:Summable (fun k:ℤ=>4*tailBound c/(k:ℝ)^2):=by
    simpa only [div_eq_mul_inv,one_mul] using
      (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*tailBound c)
  apply Summable.of_norm_bounded major
  intro k
  exact actual_alias_uniform_bound c k x (by constructor <;> linarith [(abs_le.mp inside).1,(abs_le.mp inside).2])

private theorem kernel_alias_term_read (c:BurnolCompletedMellinCoordinate)
    (k:ℤ) (x:ℝ) (inside:|x|≤q):
    kernelAliasTerm c k x=(aliasRawTerm c k x-aliasRawTerm c k 0)+
      (returnAliasTerm c k x-returnAliasTerm c k 0) := by
  by_cases zero:k=0
  · simp [kernelAliasTerm,aliasRawTerm,returnAliasTerm,zero]
  · have integer:(1:ℝ)≤|(k:ℝ)| :=by exact_mod_cast Int.one_le_abs zero
    have shifted:q < |x+k| :=by
      have distance:=shifted_distance x inside k zero
      linarith
    simp only [kernelAliasTerm,aliasRawTerm,returnAliasTerm,if_neg zero,zero_add]
    rw [actual_exterior_field c _ shifted,actual_exterior_field c _ (by linarith)]
    ring

theorem actual_kernel_alias_absolute (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:|x|≤q):Summable (fun k:ℤ=>‖kernelAliasTerm c k x‖) := by
  apply Summable.norm
  exact (((resolved_alias_summable c x inside).sub (resolved_alias_summable c 0 (by norm_num))).add
    ((return_alias_summable c x inside).sub (return_alias_summable c 0 (by norm_num)))).congr
      (fun k=>(kernel_alias_term_read c k x inside).symm)

private theorem return_alias_read (c:BurnolCompletedMellinCoordinate) (x:ℝ) (inside:|x|≤q):
    ∑'k:ℤ,returnAliasTerm c k x=
      burnolRieszReturnRaw c 0-burnolRieszReturnRaw c q-returnFourier c x := by
  have whole:=actual_return_periodization c x inside
  have split:(fun k:ℤ=>returnFourier c (x+k))=
      (fun k=>(if k=0 then returnFourier c x else 0)+returnAliasTerm c k x) := by
    funext k
    by_cases zero:k=0 <;> simp [zero,returnAliasTerm]
  rw [split,Summable.tsum_add (hasSum_ite_eq (0:ℤ) (returnFourier c x)).summable
    (return_alias_summable c x inside),tsum_ite_eq] at whole
  linear_combination whole

/-- The actual K aliases retain the original A box, all integer shifts, and the origin subtraction. -/
theorem actual_kernel_alias_read (c:BurnolCompletedMellinCoordinate) (x:ℝ) (inside:|x|≤q):
    kernelAlias c x=aliasRaw c x-aliasRaw c 0-returnFourier c x+returnFourier c 0 := by
  unfold kernelAlias
  simp_rw [kernel_alias_term_read c _ x inside]
  rw [Summable.tsum_add ((resolved_alias_summable c x inside).sub (resolved_alias_summable c 0 (by norm_num)))
    ((return_alias_summable c x inside).sub (return_alias_summable c 0 (by norm_num))),
    Summable.tsum_sub (resolved_alias_summable c x inside) (resolved_alias_summable c 0 (by norm_num)),
    Summable.tsum_sub (return_alias_summable c x inside) (return_alias_summable c 0 (by norm_num)),
    return_alias_read c x inside,return_alias_read c 0 (by norm_num)]
  change aliasRaw c x-aliasRaw c 0+_=_
  ring

theorem actual_original_regular_field (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (x:ℝ) (inside:|x|≤q):
    regularRaw c x=ForcingTail.forcingRemainder c x+InverseTail.smoothFourier c x+
      kernelAlias c x-Kernel.A c*(box x-box 0) := by
  have origin:InverseTail.smoothFourier c 0=0 := by
    unfold InverseTail.smoothFourier Constructor.fourierRaw VectorFourier.fourierIntegral
    simpa only [innerₗ_apply_apply,Real.inner_apply,mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul]
      using InverseTail.return_mean_zero c
  have zeta:riemannZeta (star c.value)=0:=by
    rw [star_def,riemannZeta_conj,zero,map_zero]
  have constant:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Constant.actual_alias_origin_constant c
  have boxZero:box 0=(1/2:ℂ):=by
    rw [box_read,Constructor.fourierRaw_integral]
    simp [Constructor.phase]
    norm_num
  rw [actual_kernel_alias_read c x inside,actual_original_A]
  unfold regularRaw returnFourier positionEndpoint
  rw [constant,zeta,origin,boxZero]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.Alias
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
