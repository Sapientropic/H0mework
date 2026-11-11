import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.UnitCounting
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKCenteredMobiusRSource.UnitTailActionSource
open scoped Topology InnerProductSpace
open private dual_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private forward_resolvent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
open private sqrt_bound from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail
local notation "q"=>(1/4:ℝ)
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "E"=>burnolQuarterZeroExtension
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "H"=>burnolUnitCountingPrimitiveL2

def powerRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=((|x|:ℝ):ℂ)^(c.value-1)

def powerProgramme (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  InfiniteWeightedProgram.program (deriv (weight (powerRaw c))) H

private theorem weight_power (c:BurnolCompletedMellinCoordinate) (u:ℝ) (positive:0<u):
    weight (powerRaw c) u=(u:ℂ)^(-c.value):=by
  rw [weight,powerRaw,abs_of_pos (inv_pos.mpr positive),Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg positive.le,div_eq_mul_inv,←Complex.cpow_neg]
  rw [show (u:ℂ)⁻¹=(u:ℂ)^(-1:ℂ) by rw [Complex.cpow_neg_one],
    ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
  congr 1
  ring

private theorem weight_derivative (c:BurnolCompletedMellinCoordinate) (u:ℝ) (positive:0<u):
    HasDerivAt (weight (powerRaw c)) ((-c.value)*(u:ℂ)^(-c.value-1)) u:=by
  have nonzero:-c.value≠0:=neg_ne_zero.mpr (ne_of_apply_ne Complex.re (by
    simpa only [Complex.zero_re] using (lt_trans (by norm_num) c.rightHalf).ne'))
  have native:=hasDerivAt_ofReal_cpow_const positive.ne' nonzero
  apply native.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds positive] with v atPositive
  exact weight_power c v atPositive

private theorem power_inputs (c:BurnolCompletedMellinCoordinate):
    (∀u:ℝ,4≤u→HasDerivAt (weight (powerRaw c)) (deriv (weight (powerRaw c)) u) u)∧
      ContinuousOn (deriv (weight (powerRaw c))) (Ici 4)∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (powerRaw c)))) (Ioi 4)∧
      Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (powerRaw c) u‖) atTop (𝓝 0):=by
  have derivative (u:ℝ) (large:4≤u):deriv (weight (powerRaw c)) u=(-c.value)*(u:ℂ)^(-c.value-1):=
    (weight_derivative c u (lt_of_lt_of_le (by norm_num) large)).deriv
  have regular:ContinuousOn (fun u:ℝ=>(-c.value)*(u:ℂ)^(-c.value-1)) (Ici 4):=by
    intro u large
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const u _
      (Or.inr (lt_of_lt_of_le (by norm_num) large).ne'))).continuousWithinAt
  have slopeContinuous:ContinuousOn (deriv (weight (powerRaw c))) (Ici 4):=
    regular.congr (fun u large=>derivative u large)
  have bound (u:ℝ) (large:4≤u):
      ‖deriv (weight (powerRaw c)) u‖*(Real.sqrt u+2)≤
        (3*‖c.value‖)*u^(-c.value.re-1/2):=by
    have positive:0<u:=lt_of_lt_of_le (by norm_num) large
    rw [derivative u large,norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos positive]
    have exponent:(-c.value-1).re=-c.value.re-1:=by simp only [sub_re,neg_re,one_re]
    rw [exponent]
    calc
      _≤(‖c.value‖*u^(-c.value.re-1))*(3*Real.sqrt u):=
        mul_le_mul_of_nonneg_left (sqrt_bound u large) (by positivity)
      _=(3*‖c.value‖)*(u^(-c.value.re-1)*u^(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow];ring
      _=_:=by
        rw [←Real.rpow_add positive]
        congr 2
        ring
  have domain:IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (powerRaw c)))) (Ioi 4):=by
    have dominant:IntegrableOn (fun u:ℝ=>(3*‖c.value‖)*u^(-c.value.re-1/2)) (Ioi 4):=
      (integrableOn_Ioi_rpow_of_lt (by linarith [c.rightHalf]) (by norm_num)).const_mul _
    apply dominant.mono' (((measurable_deriv _).norm.mul (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
    change ‖‖deriv (weight (powerRaw c)) u‖*(Real.sqrt u+2)‖≤_
    rw [Real.norm_of_nonneg (by positivity)]
    exact bound u large.le
  have head:Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (powerRaw c) u‖) atTop (𝓝 0):=by
    have native:=tendsto_rpow_neg_atTop (by linarith [c.rightHalf]:0<c.value.re-1/2)
    apply native.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u positive
    rw [weight_power c u positive,Complex.norm_cpow_eq_rpow_re_of_pos positive,Complex.neg_re,
      Real.sqrt_eq_rpow,←Real.rpow_add positive]
    congr 1
    ring
  exact ⟨fun u large=>(weight_derivative c u (lt_of_lt_of_le (by norm_num) large)).differentiableAt.hasDerivAt,
    slopeContinuous,domain,head⟩

/-- The native source's compact power has both actual programmes; its singular origin is paid by the half-strip. -/
theorem actual_native_power_reverse (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>DualSource.source N (E (SingularCounting.powerL2 (barC c)))) atTop
      (𝓝 (poissonPair (powerProgramme c))):=by
  obtain ⟨hd,hcont,hdom,hhead⟩:=power_inputs c
  have represents:(SingularCounting.powerL2 (barC c):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]powerRaw c:=by
    filter_upwards [SingularCounting.power_coeFn (barC c)] with x read
    rw [read]
    simp only [SingularCounting.powerRaw,powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  exact actual_compact_reverse _ _ represents (fun x _=>by simp only [powerRaw,abs_abs]) hd hcont hdom hhead

private theorem native_zero_source (c:BurnolCompletedMellinCoordinate):
    nativeUnitMuSource c 0=burnolNormalizedFirstSourceUnitTail c:=by
  apply Lp.ext
  filter_upwards [native_unit_source_zero c,burnolNormalizedFirstSourceUnitTail_coeFn c] with x native original
  exact native.trans original.symm

private theorem native_zero_value (c:BurnolCompletedMellinCoordinate):
    -F (powerProgramme c)=burnolUnitTailResponse c 4:=by
  obtain ⟨hd,hcont,hdom,hhead⟩:=power_inputs c
  have represents:(SingularCounting.powerL2 (barC c):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]powerRaw c:=by
    filter_upwards [SingularCounting.power_coeFn (barC c)] with x read
    rw [read]
    simp only [SingularCounting.powerRaw,powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  have compact (test:SchwartzMap ℝ ℂ):
      burnolRemainderSourceRead (E (SingularCounting.powerL2 (barC c))) test=
        (Lp.toTemperedDistributionCLM ℂ volume 2 (powerProgramme c)) test:=
    actual_compact_realizes _ _ represents (fun x _=>by simp only [powerRaw,abs_abs]) hd hcont hdom hhead test
  have transformed:=burnolRemainderRealization_fourier _ _ compact
  have definition:nativeUnitMuSource c 0= -T (E (SingularCounting.powerL2 (barC c))):=by
    simp only [nativeUnitMuSource,pow_zero,neg_one_smul,dividedLogColumn]
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (μ:=volume))
  ext test
  have generated:burnolRemainderSourceRead (nativeUnitMuSource c 0) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (-F (powerProgramme c))) test:=by
    rw [definition,←burnolRemainderSourceReadCLM_apply,map_neg,burnolRemainderSourceReadCLM_apply,
      transformed test,map_neg]
    rfl
  rw [native_zero_source] at generated
  exact generated.symm.trans (burnolOriginalUnitTail_realizes c test)

/-- The native Unit source itself has the original full Unit response as its complete forward strong graph. -/
theorem actual_native_unit_zero_forward (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>FiniteForcing.source N (nativeUnitMuSource c 0)) atTop
      (𝓝 (burnolUnitTailResponse c 4)):=by
  have generated:=((burnolTateReciprocalL2.continuous.tendsto _).comp (actual_native_power_reverse c)).neg
  have target:-T (poissonPair (powerProgramme c))=burnolUnitTailResponse c 4:=by
    change -T (T (F (powerProgramme c)))=_
    rw [burnolTateReciprocalL2_involutive,native_zero_value]
  rw [target] at generated
  have finite (N:ℕ):FiniteForcing.source N (nativeUnitMuSource c 0)=
      -T (DualSource.source N (E (SingularCounting.powerL2 (barC c)))):=by
    rw [nativeUnitMuSource,pow_zero,neg_one_smul,dividedLogColumn]
    change CountingDual.sourceCLM N (-T (E (SingularCounting.powerL2 (barC c))))=_
    rw [map_neg]
    have original:=congrArg T (dual_tate N (T (E (SingularCounting.powerL2 (barC c)))))
    simp only [burnolTateReciprocalL2_involutive] at original
    exact congrArg Neg.neg original.symm
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

private theorem native_source_power (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    nativeUnitMuSource c j=((burnolDirectRightResolventCLM c)^j) (nativeUnitMuSource c 0):=by
  induction j with
  | zero=>simp only [pow_zero,one_apply_eq_self]
  | succ j previous=>
    have action:=native_unit_source_action c j
    change burnolDirectRightResolventCLM c (nativeUnitMuSource c j)=nativeUnitMuSource c (j+1) at action
    rw [←action,previous,pow_succ',mul_apply_eq_comp]

private theorem forward_R (N:ℕ) (c:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    FiniteForcing.source N (burnolDirectRightResolventCLM c value)=
      burnolDirectRightResolventCLM c (FiniteForcing.source N value):=by
  have original:=forward_resolvent N (barC c) value
  change FiniteForcing.source N (burnolDirectRightResolvent (c.value/2) value)=
    burnolDirectRightResolvent (c.value/2) (FiniteForcing.source N value)
  simpa only [OriginalKSourceResolventReconstruction.sourceResolvent,
    OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] using original

private theorem forward_power (N:ℕ) (c:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    FiniteForcing.source N (((burnolDirectRightResolventCLM c)^j) value)=
      ((burnolDirectRightResolventCLM c)^j) (FiniteForcing.source N value):=by
  induction j with
  | zero=>simp only [pow_zero,one_apply_eq_self]
  | succ j previous=>
    rw [pow_succ',mul_apply_eq_comp,forward_R,previous,mul_apply_eq_comp]

/-- The same native source programme generates every full original R-Unit column. -/
theorem actual_native_unit_forward (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    Tendsto (fun N:ℕ=>FiniteForcing.source N (nativeUnitMuSource c j)) atTop
      (𝓝 (((burnolDirectRightResolventCLM c)^j) (burnolUnitTailResponse c 4))):=by
  have generated:=(((burnolDirectRightResolventCLM c)^j).continuous.tendsto _).comp
    (actual_native_unit_zero_forward c)
  have finite (N:ℕ):FiniteForcing.source N (nativeUnitMuSource c j)=
      ((burnolDirectRightResolventCLM c)^j) (FiniteForcing.source N (nativeUnitMuSource c 0)):=by
    rw [native_source_power,forward_power]
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.UnitCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
