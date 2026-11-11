import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.BoundaryWard
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingFirstCell
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.BoundaryWard OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.FixedShiftTail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
local notation "q"=>(1/4:ℝ)
local notation "E"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "A"=>sourceAnnulusCut

private theorem saturated_normalization (state:Hq) (N:ℕ) (x:ℝ) (positive:0<x)
    (covered:q≤(N:ℝ)*x):
    (∫a:ℝ in Ioc 0 (N:ℝ),compactRaw state (a*x))=
      (x:ℂ)⁻¹*(∫u:ℝ in Ioc 0 q,state u):=by
  have scaled:(∫a:ℝ in Ioc 0 (N:ℝ),compactRaw state (a*x))=
      x⁻¹ • ∫u:ℝ in Ioc 0 ((N:ℝ)*x),compactRaw state u:=by
    rw [←intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ positive.ne',zero_mul,
      intervalIntegral.integral_of_le (by positivity:(0:ℝ)≤(N:ℝ)*x)]
  have pointwise:EqOn (compactRaw state) ((Ioc 0 q).indicator (state:ℝ→ℂ)) (Ioc 0 ((N:ℝ)*x)):=by
    intro u inside
    have lower:-q≤u:=by linarith [inside.1]
    simp only [compactRaw,symmetricInterval,indicator_apply,mem_Icc,mem_Ioc,
      lower,inside.1,true_and]
  rw [scaled,setIntegral_congr_fun measurableSet_Ioc pointwise,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  simp only [Complex.real_smul,Complex.ofReal_inv]

/-- At the first cell the actual integer channel survives; all later integers vanish. -/
theorem actual_compact_first_cell (state:Hq) (N:ℕ) (two:2≤N):
    ∀ᵐx:ℝ∂volume,∀_first:q/2<x,
      DualSource.source N (E state) x=compactRaw state x-
        (x:ℂ)⁻¹*(∫u:ℝ in Ioc 0 q,state u):=by
  have channels:∀ᵐx:ℝ∂volume,∀n:{n:ℕ//n∈Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n:ℝ) (E state) x=compactRaw state ((n:ℝ)*x):=by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn _ _ (burnolQuarterZeroExtension_coe state) (n:ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.property).1)
  filter_upwards [Lp.coeFn_sub (∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n (E state))
      (∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a (E state)),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n=>ContinuousChannels.channel 1 n (E state)),
    compact_normalization_raw state N,channels] with x subtraction sumRead continuous channel first
  have positive:0<x:=by linarith
  have covered:q≤(N:ℝ)*x:=by
    have large:(2:ℝ)≤N:=by exact_mod_cast two
    nlinarith
  change ((∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n (E state))-
      ∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a (E state):BurnolL2) x=_
  rw [subtraction,Pi.sub_apply,sumRead,continuous,saturated_normalization state N x positive covered]
  congr 1
  calc
    _=∑n∈Finset.Ico 1 N,compactRaw state ((n:ℝ)*x):=by
      apply Finset.sum_congr rfl
      intro n member
      exact channel ⟨n,member⟩
    _=compactRaw state x:=by
      rw [Finset.sum_eq_single 1]
      · norm_num
      · intro n member different
        have large:(2:ℝ)≤n:=by
          have one:= (Finset.mem_Ico.mp member).1
          have natTwo:2≤n:=by omega
          exact_mod_cast natTwo
        have beyond:q<(n:ℝ)*x:=by nlinarith
        rw [compactRaw,indicator_of_notMem (show (n:ℝ)*x∉symmetricInterval q from
          fun inside=>not_le.mpr beyond inside.2)]
      · intro absent
        exact (absent (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)).elim

private theorem fixed_shrink:(1/2:ℝ)<Real.exp (-fixedShift):=by
  have square:stageZeroSonineQ^2=3:=by
    change (Real.sqrt 3)^2=3
    exact Real.sq_sqrt (by norm_num)
  have bound:stageZeroSonineQ<2:=by nlinarith [stageZeroSonineQ_pos]
  rw [Real.exp_neg,fixedShift,Real.exp_log stageZeroSonineQ_pos]
  rw [←one_div]
  apply (lt_div_iff₀ stageZeroSonineQ_pos).mpr
  linarith

private theorem fixed_half_density:
    (Real.exp (-fixedShift/2):ℂ)*(Real.exp (-fixedShift):ℂ)⁻¹=(Real.exp (fixedShift/2):ℂ):=by
  have realValue:Real.exp (-fixedShift/2)*(Real.exp (-fixedShift))⁻¹=Real.exp (fixedShift/2):=by
    rw [Real.exp_neg fixedShift,inv_inv,←Real.exp_add]
    congr 1
    ring
  exact_mod_cast realValue

/-- The same finite N retains the moved H−B first cell and its complete continuous normalization. -/
theorem actual_moving_compact_cell (state:Hq) (N:ℕ) (two:2≤N):
    (A (DualSource.source N (burnolMultiplicativeDilation (-fixedShift) (E state))):ℝ→ℂ)=ᵐ[
      volume.restrict (Ioc q 4)]fun x:ℝ=>
        (Real.exp (-fixedShift/2):ℂ)*compactRaw state (Real.exp (-fixedShift)*x)-
          (Real.exp (fixedShift/2):ℂ)*(x:ℂ)⁻¹*(∫u:ℝ in Ioc 0 q,state u):=by
  have dilation:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-fixedShift)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp (-fixedShift)) (Real.exp_ne_zero _))
  rw [dual_dilation]
  filter_upwards [ae_restrict_of_ae (sourceAnnulusCut_coeFn
      (burnolMultiplicativeDilation (-fixedShift) (DualSource.source N (E state)))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-fixedShift) (DualSource.source N (E state))),
    ae_restrict_of_ae (dilation.ae (actual_compact_first_cell state N two)),
    ae_restrict_mem measurableSet_Ioc] with x cut moved raw inside
  have positive:0<x:=by linarith [inside.1]
  have first:q/2<Real.exp (-fixedShift)*x:=by nlinarith [fixed_shrink,inside.1]
  rw [cut,if_pos (by rw [abs_of_pos positive];exact inside),moved]
  change (Real.exp ((-fixedShift)/2):ℂ)*DualSource.source N (E state) (Real.exp (-fixedShift)*x)=_
  rw [raw first,Complex.ofReal_mul,mul_inv_rev]
  calc
    _=(Real.exp (-fixedShift/2):ℂ)*compactRaw state (Real.exp (-fixedShift)*x)-
        ((Real.exp (-fixedShift/2):ℂ)*(Real.exp (-fixedShift):ℂ)⁻¹)*(x:ℂ)⁻¹*
          (∫u:ℝ in Ioc 0 q,state u):=by ring
    _=_:=by rw [fixed_half_density]

/-- The original actual compact iterate pays its own mean, while its moved point-value remains visible. -/
theorem actual_native_moving_compact (c:BurnolCompletedMellinCoordinate) (j N:ℕ) (two:2≤N):
    (A (DualSource.source N (burnolMultiplicativeDilation (-fixedShift)
      (((sourceVolterraResolvent (OriginalPrimitiveRankBalance.conjugateCoordinate c))^j)
        (E (nativeCompact c))))):ℝ→ℂ)=ᵐ[volume.restrict (Ioc q 4)]fun x:ℝ=>
        (Real.exp (-fixedShift/2):ℂ)*compactRaw (compactAt c j) (Real.exp (-fixedShift)*x)-
          (Real.exp (fixedShift/2):ℂ)*(x:ℂ)⁻¹*
            (((-2/star c.value)^j*burnolQuarterMeanCoefficient (burnolQuarterRestriction
              (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c)))/4):=by
  rw [←actual_compact_at]
  filter_upwards [actual_moving_compact_cell (compactAt c j) N two] with x source
  rw [source,actual_compact_positive_mass]

private theorem native_compact_raw (c:BurnolCompletedMellinCoordinate):
    compactRaw (nativeCompact c)=ᵐ[volume]
      (symmetricInterval q).indicator (fun x:ℝ=>OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c x-
        burnolRieszSingleFourierSourceRaw c x):=by
  have field:E (nativeCompact c)=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c-
      E (burnolRieszSingleFourierSource c: Hq):=by
    rw [nativeCompact,map_sub]
    rfl
  filter_upwards [burnolQuarterZeroExtension_coe (nativeCompact c),
    Lp.coeFn_sub (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c) (E (burnolRieszSingleFourierSource c:Hq)),
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.actual_quarter_raw c,DualSourceRaw.seedRaw_read c]
    with x extension subtraction wave source
  change E (nativeCompact c) x=compactRaw (nativeCompact c) x at extension
  rw [←extension,field,subtraction,Pi.sub_apply,wave,source,
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.quarterRaw,DualSourceRaw.seedRaw]
  change (symmetricInterval q).indicator (OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c) x-
    (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw c) x=
      (symmetricInterval q).indicator (fun u:ℝ=>OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c u-
        burnolRieszSingleFourierSourceRaw c u) x
  by_cases member:x∈symmetricInterval q
  · rw [indicator_of_mem member,indicator_of_mem member,indicator_of_mem member]
  · rw [indicator_of_notMem member,indicator_of_notMem member,indicator_of_notMem member,sub_zero]

/-- The literal H−B collar entering the original endpoint price, with the same full continuous fee. -/
theorem actual_original_moving_first_cell (c:BurnolCompletedMellinCoordinate) (N:ℕ) (two:2≤N):
    (A (DualSource.source N (burnolMultiplicativeDilation (-fixedShift) (E (nativeCompact c)))):ℝ→ℂ)=ᵐ[
      volume.restrict (Ioc q (q*stageZeroSonineQ))]fun x:ℝ=>
        (Real.exp (-fixedShift/2):ℂ)*
          (OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous.periodicRaw c (Real.exp (-fixedShift)*x)-
            burnolRieszSingleFourierSourceRaw c (Real.exp (-fixedShift)*x))-
          (Real.exp (fixedShift/2):ℂ)*(x:ℂ)⁻¹*
            (burnolQuarterMeanCoefficient (burnolQuarterRestriction
              (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c))/4):=by
  have profile:∀ᵐx:ℝ∂volume,x∈Ioc q 4→
      A (DualSource.source N (burnolMultiplicativeDilation (-fixedShift) (E (nativeCompact c)))) x=
        (Real.exp (-fixedShift/2):ℂ)*compactRaw (nativeCompact c) (Real.exp (-fixedShift)*x)-
          (Real.exp (fixedShift/2):ℂ)*(x:ℂ)⁻¹*(∫u:ℝ in Ioc 0 q,nativeCompact c u):=
    (ae_restrict_iff' measurableSet_Ioc).mp (actual_moving_compact_cell (nativeCompact c) N two)
  have mass:(∫u:ℝ in Ioc 0 q,nativeCompact c u)=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c))/4:=by
    simpa only [compactAt,pow_zero,one_apply_eq_self,burnolQuarterRestriction_zeroExtension,one_mul] using
      actual_compact_positive_mass c 0
  have dilation:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-fixedShift)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp (-fixedShift)) (Real.exp_ne_zero _))
  have endRead:Real.exp (-fixedShift)*(q*stageZeroSonineQ)=q:=by
    rw [Real.exp_neg,fixedShift,Real.exp_log stageZeroSonineQ_pos]
    field_simp [stageZeroSonineQ_pos.ne']
  have upper:stageZeroSonineQ≤2:=by
    change Real.sqrt 3≤2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  filter_upwards [ae_restrict_of_ae profile,ae_restrict_of_ae (dilation.ae (native_compact_raw c)),
    ae_restrict_mem measurableSet_Ioc] with x source raw inside
  have band:x∈Ioc q 4:=⟨inside.1,by nlinarith [inside.2]⟩
  have positive:0<x:=by linarith [inside.1]
  have scaledPositive:0<Real.exp (-fixedShift)*x:=mul_pos (Real.exp_pos _) positive
  have scaledUpper:=mul_le_mul_of_nonneg_left inside.2 (Real.exp_pos (-fixedShift)).le
  rw [endRead] at scaledUpper
  have member:Real.exp (-fixedShift)*x∈symmetricInterval q:=⟨by linarith,scaledUpper⟩
  rw [source band,mass,raw,indicator_of_mem member]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingFirstCell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
