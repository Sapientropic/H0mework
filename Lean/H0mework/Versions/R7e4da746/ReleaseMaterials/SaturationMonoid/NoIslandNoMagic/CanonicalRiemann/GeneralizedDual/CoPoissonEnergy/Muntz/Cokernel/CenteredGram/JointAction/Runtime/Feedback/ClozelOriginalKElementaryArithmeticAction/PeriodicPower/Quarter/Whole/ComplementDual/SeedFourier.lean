import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology InnerProductSpace
open private phase_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReturnedArithmeticKernel
open private box_derivative from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open private edge_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "freq" => (2*(Real.pi:ℂ))
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem half_domain (raw:ℝ→ℂ) (domain:Integrable raw μq):
    IntervalIntegrable raw volume 0 q:=by
  have full:IntervalIntegrable raw volume (-q) q:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q:ℝ)≤q)).mpr domain
  apply full.mono_set
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤q),uIcc_of_le (by norm_num : (-q:ℝ)≤q)]
  intro x inside
  exact ⟨by linarith [inside.1],inside.2⟩

private theorem even_fourier_cosine (raw:ℝ→ℂ) (domain:Integrable raw μq)
    (even:∀y:ℝ,raw (-y)=raw y) (x:ℝ):
    Constructor.fourierRaw raw x=2*∫y:ℝ in (0:ℝ)..q,
      Complex.cos (freq*(x:ℂ)*(y:ℂ))*raw y:=by
  have full:IntervalIntegrable raw volume (-q) q:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q:ℝ)≤q)).mpr domain
  have phased:IntervalIntegrable (fun y:ℝ=>Constructor.phase x y*raw y) volume (-q) q:=
    full.continuousOn_mul (Constructor.phaseContinuous x).continuousOn
  have reflected:(∫y:ℝ in (-q)..(0:ℝ),Constructor.phase x y*raw y)=
      ∫y:ℝ in (0:ℝ)..q,Constructor.phase x (-y)*raw y:=by
    have moved:=intervalIntegral.integral_comp_neg
      (f:=fun y:ℝ=>Constructor.phase x y*raw y) (a:=(0:ℝ)) (b:=q)
    rw [neg_zero] at moved
    rw [←moved]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [even]
  have left:IntervalIntegrable (fun y:ℝ=>Constructor.phase x y*raw y) volume (-q) 0:=by
    apply phased.mono_set
    rw [uIcc_of_le (by norm_num : (-q:ℝ)≤0),uIcc_of_le (by norm_num : (-q:ℝ)≤q)]
    intro y inside
    exact ⟨inside.1,by linarith [inside.2]⟩
  have right:IntervalIntegrable (fun y:ℝ=>Constructor.phase x y*raw y) volume 0 q:=
    (half_domain raw domain).continuousOn_mul (Constructor.phaseContinuous x).continuousOn
  have negative:IntervalIntegrable (fun y:ℝ=>Constructor.phase x (-y)*raw y) volume 0 q:=
    (half_domain raw domain).continuousOn_mul
      ((Constructor.phaseContinuous x).comp continuous_neg).continuousOn
  rw [Constructor.fourierRaw_integral,
    ←intervalIntegral.integral_add_adjacent_intervals left right,reflected,
    ←intervalIntegral.integral_add negative right,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [←add_mul,add_comm (Constructor.phase x (-y)),phase_pair]
  ring

private theorem power_cosine (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    Constructor.fourierRaw (powerRaw c.value) x=2*∫y:ℝ in (0:ℝ)..q,
      (y:ℂ)^(-star c.value)*Complex.cos (freq*(x:ℂ)*(y:ℂ)):=by
  rw [even_fourier_cosine _ (actual_power_integrable c.value c.belowOne)
    (fun y=>by simp only [powerRaw,abs_neg])]
  congr 1
  apply intervalIntegral.integral_congr
  intro y inside
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)] at inside
  simp only [powerRaw,abs_of_nonneg inside.1,mul_comm]

private theorem mean_power (c:BurnolCompletedMellinCoordinate):
    (1/2:ℂ)*rawMean (powerRaw c.value)=GapEuler.gapMean q c:=by
  have exponent:-1<(-star c.value).re:=by
    simp only [neg_re,star_def,conj_re]
    linarith [c.belowOne]
  have nonzero:1-star c.value≠0:=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [sub_re,one_re,star_def,conj_re,zero_re] at real
    linarith [c.belowOne]
  have atZero:=power_cosine c 0
  have source:Constructor.fourierRaw (powerRaw c.value) 0=
      ∫y:ℝ,powerRaw c.value y ∂μq:=by
    unfold Constructor.fourierRaw VectorFourier.fourierIntegral
    simp
  rw [source] at atZero
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.cos_zero,mul_one] at atZero
  rw [integral_cpow (Or.inl exponent),show -star c.value+1=1-star c.value by ring,
    Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero] at atZero
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  have power:(q:ℂ)^(1-star c.value)=(q:ℂ)^(-star c.value)*(q:ℂ):=by
    rw [show 1-star c.value=-star c.value+1 by ring,
      Complex.cpow_add _ _ (by norm_num : (q:ℂ)≠0),Complex.cpow_one]
  rw [power] at atZero
  have gapSolved:GapEuler.gapMean q c=((1/2:ℂ)*(q:ℂ)^(-star c.value))/(1-star c.value):=
    (eq_div_iff nonzero).mpr (by linear_combination gap)
  rw [gapSolved]
  unfold rawMean
  rw [atZero]
  push_cast
  ring

private def cosinePrimitive (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  ∫t:ℝ in (0:ℝ)..(q*x),(t:ℂ)^(-star c.value)*Complex.cos (freq*(t:ℂ))

private theorem scaled_power_fourier (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    (x:ℂ)^(1-star c.value)*((1/2:ℂ)*Constructor.fourierRaw (powerRaw c.value) x)=
      cosinePrimitive c x:=by
  rw [power_cosine]
  have moved:=intervalIntegral.integral_comp_mul_right
    (f:=fun t:ℝ=>(t:ℂ)^(-star c.value)*Complex.cos (freq*(t:ℂ)))
    (a:=(0:ℝ)) (b:=q) positive.ne'
  simp only [zero_mul,Complex.real_smul,Complex.ofReal_inv] at moved
  have integrands:(∫y:ℝ in (0:ℝ)..q,
      ((y*x:ℝ):ℂ)^(-star c.value)*Complex.cos (freq*((y*x:ℝ):ℂ)))=
      (x:ℂ)^(-star c.value)*∫y:ℝ in (0:ℝ)..q,
        (y:ℂ)^(-star c.value)*Complex.cos (freq*(x:ℂ)*(y:ℂ)):=by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y inside
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)] at inside
    dsimp only
    rw [Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg inside.1 positive.le]
    ring
  rw [integrands] at moved
  have power:(x:ℂ)^(1-star c.value)=(x:ℂ)*(x:ℂ)^(-star c.value):=by
    rw [show 1-star c.value=1+-star c.value by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
  unfold cosinePrimitive
  rw [power]
  have multiplied:=congrArg ((x:ℂ)*·) moved
  simp only [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne')] at multiplied
  linear_combination multiplied

private theorem cosinePrimitive_derivative (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (positive:0<x):
    HasDerivAt (cosinePrimitive c)
      ((q:ℂ)*((q*x:ℝ):ℂ)^(-star c.value)*Complex.cos (freq*((q*x:ℝ):ℂ))) x:=by
  let f:ℝ→ℂ:=fun t=>(t:ℂ)^(-star c.value)*Complex.cos (freq*(t:ℂ))
  have exponent:-1<(-star c.value).re:=by
    simp only [neg_re,star_def,conj_re]
    linarith [c.belowOne]
  have integrable:IntervalIntegrable f volume 0 (q*x):=
    (intervalIntegral.intervalIntegrable_cpow' exponent).mul_continuousOn
      (show Continuous (fun t:ℝ=>Complex.cos (freq*(t:ℂ))) by fun_prop).continuousOn
  have atUpper:ContinuousAt f (q*x):=
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (mul_pos (by norm_num) positive).ne')).mul
      (show ContinuousAt (fun t:ℝ=>Complex.cos (freq*(t:ℂ))) (q*x) by fun_prop)
  have measurable:StronglyMeasurable f:=by
    apply Measurable.stronglyMeasurable
    have power:Measurable (fun t:ℝ=>(t:ℂ)^(-star c.value)):=by
      apply measurable_of_continuousOn_compl_singleton 0
      intro t outside
      have nonzero:t≠0:=by simpa only [mem_compl_iff,mem_singleton_iff] using outside
      exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr nonzero)).continuousWithinAt
    exact power.mul (by fun_prop)
  have integrated:=intervalIntegral.integral_hasDerivAt_right integrable
    measurable.stronglyMeasurableAtFilter atUpper
  have chained:=integrated.scomp x ((hasDerivAt_id x).const_mul q)
  have normalized:HasDerivAt (cosinePrimitive c) ((q*1) • f (q*x)) x:=chained
  convert normalized using 1
  dsimp only [f,smul_eq_mul]
  rw [Complex.real_smul]
  push_cast
  ring

private theorem seed_fourier_split (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    Constructor.fourierRaw (seedRaw c.value) x=
      (1/2:ℂ)*Constructor.fourierRaw (powerRaw c.value) x-GapEuler.gapMean q c*box x:=by
  have cosineDomain:IntervalIntegrable (fun y:ℝ=>Complex.cos (freq*(x:ℂ)*(y:ℂ))) volume 0 q:=
    (show Continuous (fun y:ℝ=>Complex.cos (freq*(x:ℂ)*(y:ℂ))) by fun_prop).intervalIntegrable 0 q
  have powerDomain:IntervalIntegrable (fun y:ℝ=>(y:ℂ)^(-star c.value)*
      Complex.cos (freq*(x:ℂ)*(y:ℂ))) volume 0 q:=
    (intervalIntegral.intervalIntegrable_cpow' (by
      simp only [neg_re,star_def,conj_re]
      linarith [c.belowOne])).mul_continuousOn
        (show Continuous (fun y:ℝ=>Complex.cos (freq*(x:ℂ)*(y:ℂ))) by fun_prop).continuousOn
  have constant:Constructor.fourierRaw (fun _:ℝ=>(1:ℂ)) x=box x:=by
    rw [←Constructor.fourierRaw_state]
    exact congrFun (Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q).symm) x
  have boxCosine:=even_fourier_cosine (fun _:ℝ=>(1:ℂ)) (integrable_const _) (fun _=>rfl) x
  rw [constant] at boxCosine
  simp only [mul_one] at boxCosine
  have split:(∫y:ℝ in (0:ℝ)..q,Complex.cos (freq*(x:ℂ)*(y:ℂ))*seedRaw c.value y)=
      (1/2:ℂ)*(∫y:ℝ in (0:ℝ)..q,(y:ℂ)^(-star c.value)*Complex.cos (freq*(x:ℂ)*(y:ℂ)))-
      ((1/2:ℂ)*rawMean (powerRaw c.value))*(∫y:ℝ in (0:ℝ)..q,Complex.cos (freq*(x:ℂ)*(y:ℂ))):=by
    calc
      _=∫y:ℝ in (0:ℝ)..q,(1/2:ℂ)*((y:ℂ)^(-star c.value)*Complex.cos (freq*(x:ℂ)*(y:ℂ)))-
          ((1/2:ℂ)*rawMean (powerRaw c.value))*Complex.cos (freq*(x:ℂ)*(y:ℂ)):=by
        apply intervalIntegral.integral_congr
        intro y inside
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)] at inside
        dsimp only [seedRaw,powerRaw]
        rw [abs_of_nonneg inside.1]
        ring
      _=_:=by
        rw [intervalIntegral.integral_sub (powerDomain.const_mul _) (cosineDomain.const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  rw [even_fourier_cosine _ (actual_seed_integrable c.value c.belowOne)
    (actual_seed_even c.value),split,mean_power,power_cosine,boxCosine]
  ring

private def weightedSeed (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  (x:ℂ)^(1-star c.value)*Constructor.fourierRaw (seedRaw c.value) x

private theorem weightedSeed_read (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    weightedSeed c x=cosinePrimitive c x-
      GapEuler.gapMean q c*((x:ℂ)^(1-star c.value)*box x):=by
  rw [weightedSeed,seed_fourier_split]
  have source:=scaled_power_fourier c x positive
  linear_combination source

private theorem weightedSeed_derivative (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (positive:0<x):
    HasDerivAt (weightedSeed c)
      (-ForcingWhole.coefficient c*((x:ℂ)^(-star c.value)*Edge.raw q x)) x:=by
  have power:=burnolMellinTailPower_hasDerivAt (star c.value-1) positive
  simp only [show -(star c.value-1)=1-star c.value by ring,
    show -(star c.value-1+1)=-star c.value by ring] at power
  have generated:=(cosinePrimitive_derivative c x positive).sub
    ((power.mul (box_derivative x positive.ne')).const_mul (GapEuler.gapMean q c))
  have realPower:(x:ℂ)^(1-star c.value)=(x:ℂ)^(-star c.value)*(x:ℂ):=by
    rw [show 1-star c.value=-star c.value+1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
  have scalePower:((q*x:ℝ):ℂ)^(-star c.value)=
      (q:ℂ)^(-star c.value)*(x:ℂ)^(-star c.value):=by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤q) positive.le]
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  have edge:=Edge.raw_apply q x
  rw [phase_pair] at edge
  have cosine:Complex.cos (freq*((q*x:ℝ):ℂ))=Complex.cos (freq*(x:ℂ)*(q:ℂ)):=by
    congr 1
    push_cast
    ring
  have fraction:(x:ℂ)^(-star c.value)*(x:ℂ)*(Edge.raw q x/(x:ℂ))=
      (x:ℂ)^(-star c.value)*Edge.raw q x:=by
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  have normalized:HasDerivAt
      (fun y:ℝ=>cosinePrimitive c y-GapEuler.gapMean q c*((y:ℂ)^(1-star c.value)*box y))
      (-ForcingWhole.coefficient c*((x:ℂ)^(-star c.value)*Edge.raw q x)) x:=by
    convert! generated using 1
    rw [realPower,scalePower,fraction,cosine]
    unfold ForcingWhole.coefficient
    linear_combination (2*(q:ℂ)*(x:ℂ)^(-star c.value)*Complex.cos (freq*(x:ℂ)*(q:ℂ)))*gap+
      ((1-star c.value)*GapEuler.gapMean q c*(x:ℂ)^(-star c.value))*edge
  apply normalized.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds positive] with y hy
  exact weightedSeed_read c y hy

/-- The original L¹ seed pays the complete homogeneous Fourier source, including its original mean. -/
theorem actual_seed_fourier_balance (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    ForcingWhole.raw c x+Constructor.fourierRaw (seedRaw c.value) x=
      ForcingPrimitive.leadingCoefficient c*(x:ℂ)^(star c.value-1):=by
  have exponent:0<(1-star c.value).re:=by
    simp only [sub_re,one_re,star_def,conj_re]
    linarith [c.belowOne]
  have continuous:Continuous (weightedSeed c):=
    (Complex.continuous_ofReal_cpow_const exponent).mul
      (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne))
  have integrated:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le positive.le
    continuous.continuousOn (fun y hy=>weightedSeed_derivative c y hy.1)
    ((edge_integrable c 0 x).const_mul (-ForcingWhole.coefficient c))
  rw [intervalIntegral.integral_const_mul] at integrated
  have atZero:weightedSeed c 0=0:=by
    have nonzero:1-star c.value≠0:=by
      intro equal
      rw [equal,Complex.zero_re] at exponent
      exact lt_irrefl 0 exponent
    rw [weightedSeed,Complex.ofReal_zero,Complex.zero_cpow nonzero,zero_mul]
  rw [atZero,sub_zero] at integrated
  have whole:=ForcingPrimitive.weighted_forcing c x positive
  have scaled:(x:ℂ)^(1-star c.value)*
      (ForcingWhole.raw c x+Constructor.fourierRaw (seedRaw c.value) x)=
      ForcingPrimitive.leadingCoefficient c:=by
    change -ForcingWhole.coefficient c*ForcingPrimitive.edgePrimitive c x=weightedSeed c x at integrated
    unfold weightedSeed at integrated
    linear_combination whole-integrated
  have inverse:(x:ℂ)^(star c.value-1)*(x:ℂ)^(1-star c.value)=1:=by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
      show (star c.value-1)+(1-star c.value)=0 by ring,Complex.cpow_zero]
  have result:=congrArg ((x:ℂ)^(star c.value-1)*·) scaled
  rw [←mul_assoc,inverse,one_mul] at result
  exact result.trans (by ring)

theorem actual_seed_fourier_balance_abs (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0):
    ForcingWhole.raw c x+Constructor.fourierRaw (seedRaw c.value) x=
      ForcingPrimitive.leadingCoefficient c*((|x|:ℝ):ℂ)^(star c.value-1):=by
  rcases lt_or_gt_of_ne nonzero with negative|positive
  · have source:=actual_seed_fourier_balance c (-x) (neg_pos.mpr negative)
    rwa [ForcingWhole.raw_even,fourier_even _ (actual_seed_even c.value),←abs_of_neg negative] at source
  · simpa only [abs_of_pos positive] using actual_seed_fourier_balance c x positive

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
