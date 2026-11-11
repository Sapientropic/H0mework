import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Programme
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Point
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Lattice OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Programme
open scoped Topology InnerProductSpace ComplexConjugate
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def powerStep (c : BurnolCompletedMellinCoordinate) (n : ℕ) : ℂ :=
  powerSample c (n+1)-powerSample c n

private theorem sample_norm (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    ‖powerSample c n‖=(1/2:ℝ)*((n:ℝ)+1)^(-c.value.re) := by
  rw [powerSample,norm_mul]
  have half : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [half]
  congr 1
  have positive : (0:ℝ)<n+1 := by positivity
  simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,
    neg_re,star_def,conj_re] using Complex.norm_cpow_eq_rpow_re_of_pos positive (-star c.value)

/-- The variation is paid by the actual complex power derivative, including its imaginary exponent. -/
theorem actual_power_step_bound (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    ‖powerStep c n‖≤(‖c.value‖/2)*((n:ℝ)+1)^(-c.value.re-1) := by
  let f : ℝ→ℂ := fun t=>(1/2:ℂ)*(t:ℂ)^(-star c.value)
  let df : ℝ→ℂ := fun t=>(1/2:ℂ)*(-star c.value)*(t:ℂ)^(-star c.value-1)
  have exponent : -star c.value≠0 := by
    intro same
    have realPart:=congrArg Complex.re same
    simp only [neg_re,star_def,conj_re,zero_re] at realPart
    linarith [c.rightHalf]
  have differentiable : ∀ x∈Icc ((n:ℝ)+1) ((n:ℝ)+2),
      HasDerivWithinAt f (df x) (Icc ((n:ℝ)+1) ((n:ℝ)+2)) x := by
    intro x member
    have positive : 0<x := lt_of_lt_of_le (by positivity) member.1
    have source:=(hasDerivAt_ofReal_cpow_const positive.ne' exponent).const_mul (1/2:ℂ)
    simpa only [df,mul_assoc] using source.hasDerivWithinAt
  have bounded : ∀ x∈Ico ((n:ℝ)+1) ((n:ℝ)+2),
      ‖df x‖≤(‖c.value‖/2)*((n:ℝ)+1)^(-c.value.re-1) := by
    intro x member
    have positive : 0<x := lt_of_lt_of_le (by positivity) member.1
    have half : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
    simp only [df,norm_mul,norm_neg,norm_star,half]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [sub_re,neg_re,star_def,conj_re,one_re]
    have monotonePower:=Real.rpow_le_rpow_of_nonpos (by positivity:(0:ℝ)<n+1)
      member.1 (by linarith [c.rightHalf]:-c.value.re-1≤0)
    calc
      (1/2:ℝ)*‖c.value‖*x^(-c.value.re-1)=(‖c.value‖/2)*x^(-c.value.re-1) := by ring
      _≤_ := mul_le_mul_of_nonneg_left monotonePower (by positivity:(0:ℝ)≤‖c.value‖/2)
  have result:=norm_image_sub_le_of_norm_deriv_le_segment' differentiable bounded
    ((n:ℝ)+2) (by constructor <;> linarith)
  simpa only [f,powerStep,powerSample,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℂ)+1=2 by norm_num,show ((n:ℝ)+2)-((n:ℝ)+1)=1 by ring,mul_one,
    Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,Complex.ofReal_one] using result

theorem actual_power_step_summable (c : BurnolCompletedMellinCoordinate) :
    Summable (fun n:ℕ=>‖powerStep c n‖) := by
  have base : Summable (fun n:ℕ=>(n:ℝ)^(-c.value.re-1)) :=
    Real.summable_nat_rpow.mpr (by linarith [c.rightHalf])
  have shifted : Summable (fun n:ℕ=>((n:ℝ)+1)^(-c.value.re-1)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      base.comp_injective (add_left_injective (1:ℕ))
  exact (shifted.mul_left (‖c.value‖/2)).of_nonneg_of_le
    (fun _=>norm_nonneg _) (actual_power_step_bound c)

theorem actual_power_sample_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (powerSample c) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have base : Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have source:=((tendsto_rpow_neg_atTop (by linarith [c.rightHalf]:0<c.value.re)).comp base).const_mul (1/2:ℝ)
  simpa only [Function.comp_def,sample_norm,mul_zero] using source

def positivePrefix (c : BurnolCompletedMellinCoordinate) (z : ℂ) (N : ℕ) : ℂ :=
  ∑n∈Finset.range N,powerSample c n*z^(n+1)

def positiveValue (c : BurnolCompletedMellinCoordinate) (z : ℂ) : ℂ :=
  (powerSample c 0*z+∑'n:ℕ,powerStep c n*z^(n+2))/(1-z)

private theorem finite_difference (c : BurnolCompletedMellinCoordinate) (z : ℂ) (N : ℕ) :
    (1-z)*positivePrefix c z (N+1)=
      powerSample c 0*z+(∑n∈Finset.range N,powerStep c n*z^(n+2))-powerSample c N*z^(N+2) := by
  induction N with
  | zero => simp [positivePrefix];ring
  | succ N ih =>
    rw [positivePrefix,Finset.sum_range_succ]
    change (1-z)*(positivePrefix c z (N+1)+powerSample c (N+1)*z^(N+1+1))=_
    rw [mul_add,ih,Finset.sum_range_succ,powerStep]
    simp only [show N+1+1=N+2 by omega,show N+1+2=N+2+1 by omega,pow_succ]
    ring

theorem actual_positive_point_limit (c : BurnolCompletedMellinCoordinate) (z : ℂ)
    (unit : ‖z‖=1) (nontrivial : z≠1) :
    Tendsto (positivePrefix c z) atTop (𝓝 (positiveValue c z)) := by
  have bound (n:ℕ) : ‖powerStep c n*z^(n+2)‖≤‖powerStep c n‖ := by
    simp only [norm_mul,norm_pow,unit,one_pow,mul_one,le_refl]
  have summable : Summable (fun n:ℕ=>powerStep c n*z^(n+2)) :=
    Summable.of_norm_bounded (actual_power_step_summable c) bound
  have vanish : Tendsto (fun N:ℕ=>powerSample c N*z^(N+2)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_mul,norm_pow,unit,one_pow,mul_one] using
      tendsto_zero_iff_norm_tendsto_zero.mp (actual_power_sample_tendsto c)
  have head : Tendsto (fun _:ℕ=>powerSample c 0*z) atTop (𝓝 (powerSample c 0*z)) := tendsto_const_nhds
  have whole:=((head.add summable.hasSum.tendsto_sum_nat).sub vanish).div_const (1-z)
  have nonzero : 1-z≠0 := sub_ne_zero.mpr nontrivial.symm
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert whole using 1
  · funext N
    rw [←finite_difference, mul_div_cancel_left₀ _ nonzero]
  · simp only [sub_zero,positiveValue]


private theorem fourier_nat (x : AddCircle (1:ℝ)) (n : ℕ) :
    _root_.fourier (n:ℤ) x=(_root_.fourier 1 x)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,_root_.fourier_zero,pow_zero]
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,_root_.fourier_add,ih,pow_succ]

private theorem finite_split (c : BurnolCompletedMellinCoordinate) (x : AddCircle (1:ℝ)) (N : ℕ) :
    finiteMap c (N+1) x=positivePrefix c (_root_.fourier 1 x) N+
      positivePrefix c (conj (_root_.fourier 1 x)) (N+1) := by
  have step (N:ℕ) : finiteMap c (N+1) x=finiteMap c N x+
      powerCoefficient c N*(_root_.fourier 1 x)^N+
      powerSample c N*(conj (_root_.fourier 1 x))^(N+1) := by
    have negative : powerCoefficient c (-((N:ℤ)+1))=powerSample c N :=
      (powerCoefficient_even c ((N:ℤ)+1)).trans (powerCoefficient_positive c N)
    have positive : _root_.fourier ((N:ℤ)+1) x=(_root_.fourier 1 x)^(N+1) := by
      simpa only [Nat.cast_add,Nat.cast_one] using fourier_nat x (N+1)
    simp only [finiteMap,Finset.sum_range_succ,ContinuousMap.add_apply,
      ContinuousMap.smul_apply,smul_eq_mul,negative,_root_.fourier_neg,positive,
      fourier_nat,map_pow]
    ring
  induction N with
  | zero =>
    rw [step]
    simp only [finiteMap,Finset.range_zero,Finset.sum_empty,ContinuousMap.zero_apply,
      Nat.cast_zero,powerCoefficient_zero,zero_mul,zero_add,positivePrefix,
      Finset.sum_range_one,zero_add,pow_one]
  | succ N ih =>
    rw [step,ih]
    simp only [Nat.cast_add,Nat.cast_one,powerCoefficient_positive,positivePrefix,
      Finset.sum_range_succ]
    ring

def pointRaw (c : BurnolCompletedMellinCoordinate) (x : AddCircle (1:ℝ)) : ℂ :=
  positiveValue c (_root_.fourier 1 x)+positiveValue c (conj (_root_.fourier 1 x))

private theorem phase_norm (x : AddCircle (1:ℝ)) : ‖_root_.fourier 1 x‖=1 :=
  Circle.norm_coe _

private theorem conjugate_nontrivial (z : ℂ) (nontrivial : z≠1) : conj z≠1 := by
  intro same
  apply nontrivial
  change star z=1 at same
  simpa only [star_star,star_one] using congrArg (star:ℂ→ℂ) same

/-- At each nontrivial additive character the literal programme has an ordinary pointwise limit. -/
theorem actual_programme_point_limit (c : BurnolCompletedMellinCoordinate) (x : AddCircle (1:ℝ))
    (nontrivial : _root_.fourier 1 x≠1) :
    Tendsto (fun N:ℕ=>finiteMap c N x) atTop (𝓝 (pointRaw c x)) := by
  have positive:=actual_positive_point_limit c (_root_.fourier 1 x) (phase_norm x) nontrivial
  have negative:=actual_positive_point_limit c (conj (_root_.fourier 1 x))
    (by simpa only [norm_conj] using phase_norm x) (conjugate_nontrivial _ nontrivial)
  have shifted:=negative.comp (tendsto_add_atTop_nat 1)
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert positive.add shifted using 1
  · funext N
    exact finite_split c x N
  · rfl

private theorem positive_continuousAt (c : BurnolCompletedMellinCoordinate)
    (phase : AddCircle (1:ℝ)→ℂ) (continuous : Continuous phase)
    (unit : ∀ x,‖phase x‖=1) (x : AddCircle (1:ℝ)) (nontrivial : phase x≠1) :
    ContinuousAt (fun y=>positiveValue c (phase y)) x := by
  have rows (n:ℕ) : Continuous (fun y=>powerStep c n*(phase y)^(n+2)) :=
    continuous_const.mul (continuous.pow _)
  have bound (n:ℕ) (y:AddCircle (1:ℝ)) :
      ‖powerStep c n*(phase y)^(n+2)‖≤‖powerStep c n‖ := by
    simp only [norm_mul,norm_pow,unit,one_pow,mul_one,le_refl]
  have series:=continuous_tsum rows (actual_power_step_summable c) bound
  exact ((continuous_const.mul continuous).add series).continuousAt.div
    (continuous_const.sub continuous).continuousAt (sub_ne_zero.mpr nontrivial.symm)

theorem actual_point_raw_continuousAt (c : BurnolCompletedMellinCoordinate)
    (x : AddCircle (1:ℝ)) (nontrivial : _root_.fourier 1 x≠1) :
    ContinuousAt (pointRaw c) x := by
  have positive:=positive_continuousAt c (_root_.fourier 1) (_root_.fourier 1).continuous
    phase_norm x nontrivial
  have negative:=positive_continuousAt c (fun y=>conj (_root_.fourier 1 y))
    (Complex.continuous_conj.comp (_root_.fourier 1).continuous)
    (fun y=>by simpa only [norm_conj] using phase_norm y) x (conjugate_nontrivial _ nontrivial)
  exact positive.add negative

private theorem phase_nontrivial (x : AddCircle (1:ℝ)) (nonzero : x≠0) :
    _root_.fourier 1 x≠1 := by
  intro same
  apply nonzero
  apply AddCircle.injective_toCircle (by norm_num:(1:ℝ)≠0)
  apply Subtype.ext
  simpa only [_root_.fourier_one,AddCircle.toCircle_zero,Circle.coe_one] using same

/-- Strong L² and actual pointwise programme limits identify this locally continuous representative. -/
theorem actual_point_raw_representative (c : BurnolCompletedMellinCoordinate) :
    (periodicPower c:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle]pointRaw c := by
  obtain ⟨ns,monotone,limit⟩:=
    (tendstoInMeasure_of_tendsto_Lp (actual_programme_tendsto c)).exists_seq_tendsto_ae
  have representatives : ∀ᵐ x∂AddCircle.haarAddCircle,∀ N:ℕ,
      finiteSource c N x=finiteMap c N x :=
    ae_all_iff.mpr (actual_programme_representative c)
  have volume_same : (volume:Measure (AddCircle (1:ℝ)))=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using
      (AddCircle.volume_eq_smul_haarAddCircle (T:=(1:ℝ)))
  have atom : AddCircle.haarAddCircle ({0}:Set (AddCircle (1:ℝ)))=0 := by
    have measure:=AddCircle.volume_closedBall (T:=(1:ℝ)) (x:=(0:AddCircle (1:ℝ))) 0
    simpa only [Metric.closedBall_zero,volume_same,mul_zero,
      min_eq_right (by norm_num:(0:ℝ)≤1),ENNReal.ofReal_zero] using measure
  have nonzero : ∀ᵐ x:AddCircle (1:ℝ)∂AddCircle.haarAddCircle,x≠0 :=
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_eq_eq_singleton] using atom)
  filter_upwards [representatives,nonzero,limit] with x representative nonzero pointLimit
  have pointwise:=(actual_programme_point_limit c x (phase_nontrivial x nonzero)).comp monotone.tendsto_atTop
  have same : (fun N:ℕ=>finiteSource c (ns N) x)=(fun N:ℕ=>finiteMap c (ns N) x) :=
    funext fun N=>representative (ns N)
  rw [same] at pointLimit
  exact tendsto_nhds_unique pointLimit pointwise

end OriginalKElementaryArithmeticAction.PeriodicPower.Point
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
