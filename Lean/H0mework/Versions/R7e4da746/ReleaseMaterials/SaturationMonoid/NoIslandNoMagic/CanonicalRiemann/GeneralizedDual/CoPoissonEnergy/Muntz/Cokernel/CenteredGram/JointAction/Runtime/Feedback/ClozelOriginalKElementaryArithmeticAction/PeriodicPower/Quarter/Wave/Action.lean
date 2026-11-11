import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open scoped Topology ENNReal InnerProductSpace
open private box_derivative coefficient_eq_jump companion_continuous from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open private box_fourier_trig from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
local notation "q" => (1/4:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)
local notation "window" => Icc (-(1/2):ℝ) (1/2:ℝ)
local notation "interval" => Icc (-q) q
local notation "cell" => Ioc (-q) q
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2

private theorem box_even (x : ℝ) : box (-x)=box x := by
  by_cases zero:x=0
  · subst x;simp
  · rw [box_fourier_trig (-x) (neg_ne_zero.mpr zero),box_fourier_trig x zero]
    simp only [Complex.ofReal_neg,mul_neg,Complex.sin_neg,div_neg,neg_div,neg_neg]

private theorem resolved_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    resolvedFourierRaw c (-x)=resolvedFourierRaw c x := by
  rw [resolvedFourierRaw,resolvedFourierRaw,ForcingWhole.raw_even,box_even]

private theorem alias_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) : aliasRaw c (-x)=aliasRaw c x := by
  unfold aliasRaw
  rw [←(Equiv.neg ℤ).tsum_eq (fun k:ℤ=>aliasRawTerm c k (-x))]
  apply tsum_congr
  intro k
  by_cases zero:k=0
  · subst k;simp [aliasRawTerm]
  · simp only [Equiv.neg_apply,aliasRawTerm,neg_eq_zero,zero,if_false,Int.cast_neg]
    rw [show -x+ -(k:ℝ)= -(x+k) by ring,resolved_even]

theorem actual_periodic_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    periodicRaw c (-x)=periodicRaw c x := by
  rw [periodicRaw,periodicRaw,resolved_even,alias_even]

private theorem box_source : Constructor.fourierRaw (fun _:ℝ=>(1:ℂ))=box := by
  funext x
  have raw:=congrFun (Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)) x
  rw [Constructor.fourierRaw_state] at raw
  exact raw.symm

private def regularRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  aliasRaw c x-jumpCoefficient c*box x-resolvedRaw c 0
private def regularSlope (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  aliasSlope c x-jumpCoefficient c*Constructor.fourierDerivative (fun _:ℝ=>(1:ℂ)) x

private theorem regular_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (regularRaw c) window :=
  ((actual_alias_raw_continuous c).sub (continuousOn_const.mul
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)).continuousOn)).sub continuousOn_const

private theorem regular_slope_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (regularSlope c) window :=
  (actual_alias_slope_continuous c).sub (continuousOn_const.mul
    (Constructor.fourierDerivative_continuous (fun _:ℝ=>(1:ℂ)) continuous_const).continuousOn)

private theorem regular_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x∈interval) : HasDerivAt (regularRaw c) (regularSlope c x) x := by
  have boxSource:=Constructor.fourierRaw_hasDerivAt (fun _:ℝ=>(1:ℂ)) continuous_const x
  rw [box_source] at boxSource
  exact ((actual_alias_derivative c x (by constructor <;> linarith [inside.1,inside.2])).sub
    (boxSource.const_mul (jumpCoefficient c))).sub_const (resolvedRaw c 0)

private theorem raw_split (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    periodicRaw c x=ForcingWhole.raw c x+regularRaw c x := by
  unfold periodicRaw resolvedFourierRaw regularRaw
  ring

private theorem companion_split (c : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    ForcingWhole.coefficient c*Edge.raw q x+(x:ℂ)*regularSlope c x-
        (star c.value-1)*regularRaw c x=companionRaw c x := by
  have boxSource:=Constructor.fourierRaw_hasDerivAt (fun _:ℝ=>(1:ℂ)) continuous_const x
  rw [box_source] at boxSource
  have source:=boxSource.unique (box_derivative x nonzero)
  unfold regularSlope regularRaw companionRaw
  rw [source,coefficient_eq_jump]
  field_simp [Complex.ofReal_ne_zero.mpr nonzero]
  ring

private theorem regular_interval (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (∫ x:ℝ in cell, ((x:ℂ)*regularRaw c x)*deriv test x+
      (regularRaw c x+(x:ℂ)*regularSlope c x)*test x)=
        (q:ℂ)*regularRaw c q*test q-(-q:ℝ)*regularRaw c (-q)*test (-q) := by
  have subset : interval⊆window := by intro x hx;constructor <;> linarith [hx.1,hx.2]
  have rc:ContinuousOn (regularRaw c) interval:=(regular_continuous c).mono subset
  have rd:ContinuousOn (regularSlope c) interval:=(regular_slope_continuous c).mono subset
  have dc:Continuous (fun x:ℝ=>deriv test x):=(SchwartzMap.derivCLM ℂ ℂ test).continuous
  have integrable:IntervalIntegrable (fun x:ℝ=>((x:ℂ)*regularRaw c x)*deriv test x+
      (regularRaw c x+(x:ℂ)*regularSlope c x)*test x) volume (-q) q :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le (by norm_num : -q≤q)]
      exact ((Complex.continuous_ofReal.continuousOn.mul rc).mul dc.continuousOn).add
        ((rc.add (Complex.continuous_ofReal.continuousOn.mul rd)).mul test.continuous.continuousOn))
  have source:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun x:ℝ=>(x:ℂ)*regularRaw c x*test x)
    (fun x hx=>by
      have inside:x∈interval:=by simpa only [uIcc_of_le (by norm_num : -q≤q)] using hx
      have derivative:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul (regular_derivative c x inside)).mul (test.hasDerivAt x)
      convert! derivative using 1
      simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,Pi.mul_apply]
      ring) integrable
  rw [intervalIntegral.integral_of_le (by norm_num : -q≤q)] at source
  exact source

private theorem raw_mul_integrable (c : BurnolCompletedMellinCoordinate) (f : ℝ→ℂ)
    (continuous : Continuous f) : IntegrableOn (fun x:ℝ=>periodicRaw c x*f x) cell := by
  have old:IntegrableOn (fun x:ℝ=>ForcingWhole.raw c x*f x) cell :=
    ((LocallyIntegrable.mul_continuous continuous (ForcingWhole.raw_local c)).integrableOn_isCompact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have regular:IntegrableOn (fun x:ℝ=>regularRaw c x*f x) cell :=
    (((regular_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])).mul
      continuous.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply (old.add regular).congr_fun _ measurableSet_Ioc
  intro x _
  dsimp only [Pi.add_apply]
  rw [raw_split]
  ring

/-- The original quarter zero removes both actual boundary terms in the whole Euler source. -/
theorem actual_quarter_weak (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x:ℝ in cell, ((x:ℂ)*periodicRaw c x)*deriv test x+
      (star c.value*periodicRaw c x+companionRaw c x)*test x)=0 := by
  let old:=fun x:ℝ=>((x:ℂ)*ForcingWhole.raw c x)*deriv test x+
    (star c.value*ForcingWhole.raw c x+ForcingWhole.coefficient c*Edge.raw q x)*test x
  let regular:=fun x:ℝ=>((x:ℂ)*regularRaw c x)*deriv test x+
    (regularRaw c x+(x:ℂ)*regularSlope c x)*test x
  have dc:Continuous (fun x:ℝ=>deriv test x):=(SchwartzMap.derivCLM ℂ ℂ test).continuous
  have oldLocal:LocallyIntegrable old :=
    (LocallyIntegrable.mul_continuous dc
      (LocallyIntegrable.continuous_mul Complex.continuous_ofReal (ForcingWhole.raw_local c))).add
      (LocallyIntegrable.mul_continuous test.continuous
        ((LocallyIntegrable.continuous_mul continuous_const (ForcingWhole.raw_local c)).add
          ((Edge.raw_continuous q).const_mul (ForcingWhole.coefficient c)).locallyIntegrable))
  have rc:ContinuousOn (regularRaw c) interval:=
    (regular_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  have rd:ContinuousOn (regularSlope c) interval:=
    (regular_slope_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  have regularC:ContinuousOn regular interval:=
    ((Complex.continuous_ofReal.continuousOn.mul rc).mul dc.continuousOn).add
      ((rc.add (Complex.continuous_ofReal.continuousOn.mul rd)).mul test.continuous.continuousOn)
  have combine:(∫ x:ℝ in cell, ((x:ℂ)*periodicRaw c x)*deriv test x+
      (star c.value*periodicRaw c x+companionRaw c x)*test x)=
      (∫x:ℝ in cell,old x)+(∫x:ℝ in cell,regular x) := by
    rw [←integral_add ((oldLocal.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self)
      (regularC.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s:=cell) (volume.ae_ne (0:ℝ))] with x nonzero
    rw [raw_split,←companion_split c x nonzero]
    dsimp only [old,regular]
    ring
  rw [combine]
  change (∫x:ℝ in cell,old x)+(∫x:ℝ in cell,regular x)=0
  dsimp only [old,regular]
  rw [ForcingWhole.raw_interval_ibp,regular_interval]
  have right:=actual_original_periodic_zero_quarter c zero
  have left:periodicRaw c (-q)=0:=by rw [actual_periodic_even,right]
  rw [raw_split] at right left
  rw [ForcingWhole.raw_even] at left
  push_cast
  linear_combination (norm:=ring_nf) (1/4:ℂ)*test q*right+(1/4:ℂ)*test (-q)*left

theorem actual_quarter_euler (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    GapEuler.euler (quarterWave c:TemperedDistribution ℝ ℂ)=(velocity c:TemperedDistribution ℝ ℂ) := by
  ext test
  have weak:=actual_quarter_weak c zero test
  have firstI:IntegrableOn (fun x:ℝ=>((x:ℂ)*periodicRaw c x)*deriv test x) cell := by
    convert raw_mul_integrable c (fun x:ℝ=>(x:ℂ)*deriv test x)
      (Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous) using 1
    funext x;ring
  have secondI:IntegrableOn (fun x:ℝ=>star c.value*(periodicRaw c x*test x)) cell:=
    (raw_mul_integrable c test test.continuous).const_mul (star c.value)
  have thirdI:IntegrableOn (fun x:ℝ=>companionRaw c x*test x) cell:=
    (((companion_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])).mul
      test.continuous.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have split:(∫x:ℝ in cell,((x:ℂ)*periodicRaw c x)*deriv test x+
      (star c.value*periodicRaw c x+companionRaw c x)*test x)=
      (∫x:ℝ in cell,((x:ℂ)*periodicRaw c x)*deriv test x)+
      star c.value*(∫x:ℝ in cell,periodicRaw c x*test x)+
      (∫x:ℝ in cell,companionRaw c x*test x) := by
    rw [←integral_const_mul,←integral_add firstI secondI]
    rw [←integral_add (f:=fun x:ℝ=>((x:ℂ)*periodicRaw c x)*deriv test x+
      star c.value*(periodicRaw c x*test x)) (g:=fun x:ℝ=>companionRaw c x*test x)
      (firstI.add secondI) thirdI]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [split] at weak
  change GapEuler.euler (E (periodicQuarter c):TemperedDistribution ℝ ℂ) test=_
  rw [ForcingCutoff.euler_zeroExtension_pairing _ _ (actual_periodic_quarter_raw c)]
  change _=Lp.toTemperedDistributionCLM ℂ volume 2 ((star c.value-1/2) • quarterWave c+companion c) test
  rw [map_add,map_smul]
  simp only [add_apply,smul_apply,smul_eq_mul,Lp.toTemperedDistributionCLM_apply]
  rw [show quarterWave c=E (periodicQuarter c) from rfl,
    show companion c=E (companionQuarter c) from rfl,
    ForcingCutoff.zeroExtension_pairing _ _ (actual_periodic_quarter_raw c),
    ForcingCutoff.zeroExtension_pairing _ _ (actual_companion_raw c)]
  linear_combination -weak

/-- The generated compact companion drives the original full strong dilation, with no domain input. -/
theorem actual_quarter_strong (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    HasDerivAt (fun h:ℝ=>burnolMultiplicativeDilation h (quarterWave c)) (velocity c) 0 :=
  DilationWard.strong_derivative _ _ (actual_quarter_euler c zero)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
