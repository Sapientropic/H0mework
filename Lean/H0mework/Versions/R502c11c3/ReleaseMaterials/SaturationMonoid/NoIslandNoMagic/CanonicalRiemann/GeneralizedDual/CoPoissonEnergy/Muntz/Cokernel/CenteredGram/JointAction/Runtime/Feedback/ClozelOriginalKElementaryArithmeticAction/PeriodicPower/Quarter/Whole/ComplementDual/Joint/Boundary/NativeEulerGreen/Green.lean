import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SameNArithmeticGreenResolvent

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen
open Complex Filter FourierTransform MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace ENNReal ContDiff
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "C" => ConstantDual.seed
local notation "leading" => ForcingPrimitive.leadingCoefficient
local instance greenFiniteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)
open private constant_euler from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SameNArithmeticGreenResolvent
open private window_pairing_eq_truncated edge_wave_eq_raw from
  H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.SourceKernel
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw

def rate (c:BurnolCompletedMellinCoordinate):ℂ:=star c.value-1/2

def powerBeta (c:BurnolCompletedMellinCoordinate):ℂ:=
  SingularCounting.powerRaw c q-burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)

private theorem edge_read : GapEuler.edge q=(q:ℂ) •
    (TemperedDistribution.delta q+TemperedDistribution.delta (-q))-(C:TemperedDistribution ℝ ℂ) := by
  ext test
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,TemperedDistribution.delta_apply]
  rw [Translator.ForcingCutoff.edge_pairing]
  change _=(q:ℂ)*(test q+test (-q))-(E (intervalConstant q):TemperedDistribution ℝ ℂ) test
  rw [Translator.ForcingCutoff.zeroExtension_pairing _ _ (intervalConstant_coeFn q)]
  simp only [one_mul]

theorem centered_power_euler (c:BurnolCompletedMellinCoordinate) :
    GapEuler.euler (E (SingularCounting.centeredPower c:Hq):TemperedDistribution ℝ ℂ)=
      rate c • (E (SingularCounting.centeredPower c:Hq):TemperedDistribution ℝ ℂ)-
        powerBeta c • GapEuler.edge q := by
  let mean:=burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)
  have centered:(E (SingularCounting.centeredPower c:Hq):TemperedDistribution ℝ ℂ)=
      (E (SingularCounting.powerL2 c):TemperedDistribution ℝ ℂ)-mean • (C:TemperedDistribution ℝ ℂ) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2 (E (Constructor.zeroMean _ :Hq))=_
    rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul]
    rfl
  have source:=power_euler c
  have meanSource:=power_mean c
  change star c.value*mean=SingularCounting.powerRaw c q at meanSource
  rw [centered,map_sub,map_smul,source,constant_euler,edge_read]
  unfold rate powerBeta
  rw [←meanSource]
  module

private theorem state_integrable (state:Hq):Integrable (state:ℝ→ℂ) μq :=
  (Lp.memLp state).integrable (by norm_num)

private theorem state_moment (state:Hq):Integrable (fun x:ℝ=>‖x‖*‖state x‖) μq := by
  simpa only [mul_comm] using! IntegrableOn.mul_continuousOn (state_integrable state).norm
    (continuous_norm.continuousOn:ContinuousOn (fun x:ℝ=>‖x‖) (symmetricInterval q)) isCompact_Icc

private theorem state_fourier_moment (state:Hq):
    Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) (state:ℝ→ℂ)) μq := by
  apply ((state_moment state).const_mul (2*Real.pi*‖(innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖)).mono'
    (state_integrable state).aestronglyMeasurable.fourierSMulRight
  filter_upwards with x
  exact (VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) (state:ℝ→ℂ) x).trans_eq (by ring)

private theorem return_derivative (state:M) (x:ℝ):
    HasDerivAt (burnolMeanZeroFourierRaw state) (Constructor.fourierDerivative (state:Hq) x) x := by
  have source:=VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ)
    (state_integrable (state:Hq)) (state_moment (state:Hq)) x
  have bilinear:(innerₗ ℝ)=(innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [innerₗ_apply_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply]
  change HasDerivAt (fun y:ℝ=>burnolRadiusTruncatedFourierRaw q (state:Hq) y-
    burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq))) _ x
  unfold burnolRadiusTruncatedFourierRaw
  rw [bilinear]
  exact source.hasDerivAt.sub_const _

private theorem return_slope_continuous (state:M):
    Continuous (Constructor.fourierDerivative (state:Hq)) := by
  have same:Constructor.fourierDerivative (state:Hq)=deriv (burnolMeanZeroFourierRaw state) := by
    funext x
    exact (return_derivative state x).deriv.symm
  rw [same]
  exact (actual_return_contDiff state).continuous_deriv (by norm_num)

private theorem return_raw_continuous (state:M):Continuous (burnolMeanZeroFourierRaw state) :=
  (actual_return_contDiff state).continuous

def returnedEuler (state:M):M:=Constructor.zeroMean
  (Euler.smoothEuler (burnolMeanZeroFourierRaw state) (Constructor.fourierDerivative (state:Hq))
    (return_raw_continuous state) (return_slope_continuous state))

private theorem return_even (state:M) (even:reflectRestricted q (state:Hq)=state):
    burnolMeanZeroFourierRaw state (-q)=burnolMeanZeroFourierRaw state q := by
  unfold burnolMeanZeroFourierRaw
  rw [fourier_raw_even_of_fixed _ even]

private theorem returned_euler (state:M) (even:reflectRestricted q (state:Hq)=state):
    GapEuler.euler (E (S state:Hq):TemperedDistribution ℝ ℂ)=
      (E (returnedEuler state:Hq):TemperedDistribution ℝ ℂ)-
        burnolMeanZeroFourierRaw state q • GapEuler.edge q := by
  exact Euler.even_extension_euler (S state:Hq) _ _ (burnolMeanZeroFourier_ae_raw state)
    (return_raw_continuous state) (return_slope_continuous state) (return_derivative state)
    (Euler.smoothEuler_mean (S state) _ _ (burnolMeanZeroFourier_ae_raw state)
      (return_raw_continuous state) (return_slope_continuous state) (return_derivative state))
    (return_even state even)

private theorem slope_integral (state:Hq) (frequency:ℝ):
    Constructor.fourierDerivative state frequency=
      ∫x:ℝ in (-q)..q,Constructor.phase frequency x*
        (-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*state x) := by
  unfold Constructor.fourierDerivative
  erw [Real.fourierIntegral_continuousLinearMap_apply'
    («L» := (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) (a:=(1:ℝ)) (w:=frequency) (state_fourier_moment state)]
  rw [intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q),←integral_Icc_eq_integral_Ioc]
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  have innerOne:(innerSL ℝ) x 1=x := by rw [innerSL_apply_apply,Real.inner_apply,mul_one]
  have innerFrequency:(innerSL ℝ) x frequency=x*frequency := by rw [innerSL_apply_apply,Real.inner_apply]
  simp only [VectorFourier.fourierSMulRight_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    innerOne,innerFrequency,Circle.smul_def,smul_eq_mul,Constructor.phase,real_smul]
  rw [mul_comm x frequency]
  ring

private theorem moment_wave (state:M) (frequency:ℝ):
    (∫x:ℝ in Ioc (-q) q,((x:ℂ)*(state:Hq) x)*deriv (Euler.WindowTest.wave frequency) x)=
      (frequency:ℂ)*Constructor.fourierDerivative (state:Hq) frequency := by
  rw [slope_integral,intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q),
    ←integral_Icc_eq_integral_Ioc,←integral_const_mul]
  rw [←integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  rw [Euler.WindowTest.wave_deriv frequency inside]
  unfold Constructor.phase
  ring

private theorem kernel_ward (state db:M) (beta:ℂ)
    (source:GapEuler.euler (E (state:Hq):TemperedDistribution ℝ ℂ)=
      (E (db:Hq):TemperedDistribution ℝ ℂ)-beta • GapEuler.edge q) (frequency:ℝ):
    (frequency:ℂ)*Constructor.fourierDerivative (state:Hq) frequency+
      (1/2:ℂ)*burnolRadiusTruncatedFourierRaw q (state:Hq) frequency+
      burnolRadiusTruncatedFourierRaw q (db:Hq) frequency=beta*Edge.raw q frequency := by
  have actual:=congrArg (fun v:TemperedDistribution ℝ ℂ=>v (Euler.WindowTest.wave frequency)) source
  simp only [sub_apply,smul_apply,smul_eq_mul] at actual
  rw [Translator.ForcingCutoff.euler_zeroExtension_pairing (state:Hq) _ Filter.EventuallyEq.rfl,
    Translator.ForcingCutoff.zeroExtension_pairing (db:Hq) _ Filter.EventuallyEq.rfl,
    moment_wave,window_pairing_eq_truncated,window_pairing_eq_truncated,edge_wave_eq_raw] at actual
  linear_combination -actual

private theorem compact_congr (f g:ℝ→ℂ) (hf:Continuous f) (hg:Continuous g) (same:f=g):
    Constructor.compact f hf=Constructor.compact g hg := by
  subst g
  rfl

private theorem mean_ward (state db:M) (beta:ℂ)
    (source:GapEuler.euler (E (state:Hq):TemperedDistribution ℝ ℂ)=
      (E (db:Hq):TemperedDistribution ℝ ℂ)-beta • GapEuler.edge q):
    returnedEuler state+S db=beta • Response.eta := by
  let nativeFourier:=burnolRadiusTruncatedFourierRaw q (db:Hq)
  let mean:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq))/2
  let lhs:ℝ→ℂ:=fun x=> (x:ℂ)*Constructor.fourierDerivative (state:Hq) x+
    (1/2:ℂ)*burnolMeanZeroFourierRaw state x+nativeFourier x
  let rhs:ℝ→ℂ:=fun x=>beta*Edge.raw q x-mean
  have lhsCont:Continuous lhs := by
    have slope:=return_slope_continuous state
    have raw:=return_raw_continuous state
    have native:=burnolRadiusTruncatedFourierRaw_continuous (db:Hq)
    fun_prop
  have rhsCont:Continuous rhs := ((Edge.raw_continuous q).const_mul beta).sub continuous_const
  have same:lhs=rhs := by
    funext x
    have actual:=kernel_ward state db beta source x
    dsimp only [lhs,rhs,nativeFourier,mean]
    unfold burnolMeanZeroFourierRaw
    linear_combination actual
  have states:Constructor.compact lhs lhsCont=Constructor.compact rhs rhsCont :=
    ((Constructor.continuous_memLp lhs lhsCont).toLp_eq_toLp_iff
      (Constructor.continuous_memLp rhs rhsCont)).mpr (Filter.EventuallyEq.of_eq same)
  have lhsRead:Constructor.compact lhs lhsCont=
      Euler.smoothEuler (burnolMeanZeroFourierRaw state) (Constructor.fourierDerivative (state:Hq))
        (return_raw_continuous state) (return_slope_continuous state)+
      burnolTruncatedFourier (db:Hq) := by
    rw [←Edge.compact_truncatedFourier (db:Hq)]
    exact Constructor.compact_add _ nativeFourier
      ((Complex.continuous_ofReal.mul (return_slope_continuous state)).add
        ((return_raw_continuous state).const_mul (1/2:ℂ))) (burnolRadiusTruncatedFourierRaw_continuous _)
  rw [lhsRead] at states
  have rhsRead:Constructor.compact rhs rhsCont=
      beta • Constructor.compact (Edge.raw q) (Edge.raw_continuous q)-mean • intervalConstant q := by
    rw [←Constructor.compact_smul beta (Edge.raw q) (Edge.raw_continuous q),
      ←Constructor.compact_one,←Constructor.compact_smul mean (fun _ :ℝ=>(1:ℂ)) continuous_const,
      ←Constructor.compact_sub]
    have functions:rhs=(beta • Edge.raw q-mean • (fun _ :ℝ=>(1:ℂ))) := by
      funext x
      simp only [rhs,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_one]
    exact compact_congr rhs _ rhsCont
      (((Edge.raw_continuous q).const_smul beta).sub (continuous_const.const_smul mean)) functions
  rw [rhsRead] at states
  have normalized:=congrArg Constructor.zeroMean states
  simp only [map_add,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero] at normalized
  rw [Edge.zeroMean_raw_eq_endpointColumns] at normalized
  exact normalized


private theorem log_source (c:BurnolCompletedMellinCoordinate):
    L (logBFirst c 0)=SingularCounting.centeredPower c := by
  have source:=(log_B_source c 0).1
  change logBFirst c 0-S (S (logBFirst c 0))=SingularCounting.centeredPower c
  simpa only [logBSecond,map_neg,←sub_eq_add_neg,centeredLogColumn,dividedLogColumn,
    SingularCounting.centeredPower] using source

private theorem log_even (c:BurnolCompletedMellinCoordinate):
    reflectRestricted q (logBFirst c 0:Hq)=logBFirst c 0 := by
  exact congrArg (fun v:M=>(v:Hq)) (log_B_even c 0)

private theorem return_fixed (state:M) (even:reflectRestricted q (state:Hq)=state):
    reflectRestricted q (S state:Hq)=S state := by
  have fixed:sourceMeanZeroReflection state=state := Subtype.ext even
  have source:=sourceMeanZeroFourier_reflect state
  rw [fixed] at source
  exact congrArg (fun v:M=>(v:Hq)) source.symm

def logEuler (c:BurnolCompletedMellinCoordinate):M:=
  rate c • SingularCounting.centeredPower c+returnedEuler (S (logBFirst c 0))

def logBeta (c:BurnolCompletedMellinCoordinate):ℂ:=
  powerBeta c+burnolMeanZeroFourierRaw (S (logBFirst c 0)) q

def logGamma (c:BurnolCompletedMellinCoordinate):ℂ:=
  burnolMeanZeroFourierRaw (logBFirst c 0) q

private theorem log_weak (c:BurnolCompletedMellinCoordinate):
    GapEuler.euler (E (logBFirst c 0:Hq):TemperedDistribution ℝ ℂ)=
      (E (logEuler c:Hq):TemperedDistribution ℝ ℂ)-logBeta c • GapEuler.edge q := by
  have split:logBFirst c 0=SingularCounting.centeredPower c+S (S (logBFirst c 0)) := by
    have source:=log_source c
    change logBFirst c 0-S (S (logBFirst c 0))=SingularCounting.centeredPower c at source
    exact sub_eq_iff_eq_add.mp source
  have whole:=congrArg (fun v:M=>(E (v:Hq):TemperedDistribution ℝ ℂ)) split
  have actual:=congrArg GapEuler.euler whole
  simp only [Submodule.coe_add,←Lp.toTemperedDistributionCLM_apply,map_add] at actual
  simp only [Lp.toTemperedDistributionCLM_apply] at actual
  rw [centered_power_euler,returned_euler _ (return_fixed _ (log_even c))] at actual
  rw [actual]
  simp only [logEuler,logBeta,Submodule.coe_add,Submodule.coe_smul,
    ←Lp.toTemperedDistributionCLM_apply,map_add,map_smul]
  module

private theorem log_euler_equation (c:BurnolCompletedMellinCoordinate):
    L (logEuler c-rate c • logBFirst c 0)=
      logGamma c • Response.eta-logBeta c • S Response.eta := by
  have first:=congrArg S (mean_ward _ _ _ (log_weak c))
  rw [map_add,map_smul] at first
  have second:=mean_ward _ _ _ (returned_euler _ (log_even c))
  have build:logEuler c=rate c • SingularCounting.centeredPower c+returnedEuler (S (logBFirst c 0)) := rfl
  rw [map_sub,map_smul,log_source]
  change (logEuler c-S (S (logEuler c)))-rate c • SingularCounting.centeredPower c=_
  change returnedEuler (S (logBFirst c 0))+S (returnedEuler (logBFirst c 0))=
    logGamma c • Response.eta at second
  linear_combination (norm:=module) build+second-first

private theorem response_v_source : L Response.v=S Response.eta := by
  have source:=congrArg S Response.u_equation
  change S (Response.u-S (S Response.u))=_ at source
  rw [map_sub] at source
  exact source

/-- The original zero-log B source has its own unforced Euler row. -/
theorem log_euler (c:BurnolCompletedMellinCoordinate):
    logEuler c=rate c • logBFirst c 0+logGamma c • Response.u-logBeta c • Response.v := by
  have candidate:L (logGamma c • Response.u-logBeta c • Response.v)=
      logGamma c • Response.eta-logBeta c • S Response.eta := by
    rw [map_sub,map_smul,map_smul,Response.u_equation,response_v_source]
  have solved:=congrArg burnolMeanZeroBlockInverse ((log_euler_equation c).trans candidate.symm)
  have inverseLeft:burnolMeanZeroBlockInverse*L=1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (burnolMeanZeroBlockInverse*L) (logEuler c-rate c • logBFirst c 0)=
    (burnolMeanZeroBlockInverse*L) (logGamma c • Response.u-logBeta c • Response.v) at solved
  rw [inverseLeft] at solved
  change logEuler c-rate c • logBFirst c 0=logGamma c • Response.u-logBeta c • Response.v at solved
  linear_combination (norm:=module) solved


def logRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  SingularCounting.powerRaw c x-burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)+
    burnolMeanZeroFourierRaw (S (logBFirst c 0)) x

private theorem centered_power_read (c:BurnolCompletedMellinCoordinate):
    (SingularCounting.centeredPower c:Hq)=ᵐ[μq]
      fun x:ℝ=>SingularCounting.powerRaw c x-burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) := by
  change ((Constructor.zeroMean (SingularCounting.powerL2 c):M):ℝ→ℂ)=ᵐ[μq]_
  rw [Constructor.zeroMean_read]
  filter_upwards [Lp.coeFn_sub (SingularCounting.powerL2 c)
    (burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • intervalConstant q),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)) (intervalConstant q),
    SingularCounting.power_coeFn c,intervalConstant_coeFn q] with x subtracted scaled power unit
  rw [subtracted,Pi.sub_apply,scaled,Pi.smul_apply,smul_eq_mul,power,unit,mul_one]

private theorem log_read (c:BurnolCompletedMellinCoordinate):
    (logBFirst c 0:Hq)=ᵐ[μq]logRaw c := by
  have split:logBFirst c 0=SingularCounting.centeredPower c+S (S (logBFirst c 0)) := by
    have source:=log_source c
    change logBFirst c 0-S (S (logBFirst c 0))=SingularCounting.centeredPower c at source
    exact sub_eq_iff_eq_add.mp source
  have whole:(logBFirst c 0:Hq)=(SingularCounting.centeredPower c:Hq)+(S (S (logBFirst c 0)):Hq) :=
    congrArg (fun v:M=>(v:Hq)) split
  apply (Filter.EventuallyEq.of_eq (congrArg (fun v:Hq=>(v:ℝ→ℂ)) whole)).trans
  filter_upwards [Lp.coeFn_add (SingularCounting.centeredPower c:Hq) (S (S (logBFirst c 0)):Hq),
    centered_power_read c,burnolMeanZeroFourier_ae_raw (S (logBFirst c 0))] with x added power returned
  rw [added,Pi.add_apply,power,returned]
  rfl

def nativeRaw (c:BurnolCompletedMellinCoordinate):ℝ→ℂ:=
  centeredFourierRaw (dualRaw c.value c.belowOne)

def nativeBeta (c:BurnolCompletedMellinCoordinate):ℂ:=nativeRaw c q

def nativeGamma (c:BurnolCompletedMellinCoordinate):ℂ:=burnolMeanZeroFourierRaw (nativeSmooth c) q

def originCoefficient (c:BurnolCompletedMellinCoordinate):ℂ:=star c.value*GapEuler.gapMean q c

private theorem native_read (c:BurnolCompletedMellinCoordinate):
    (nativeSmooth c:Hq)=ᵐ[μq]nativeRaw c := by
  rw [actual_native_smooth]
  exact actual_smooth_raw _ _

private theorem generated_native_read (c:BurnolCompletedMellinCoordinate):
    (nativeSmooth c:Hq)=ᵐ[μq]fun x:ℝ=>leading c*logRaw c x-burnolRieszSingleFourierSourceRaw c x := by
  filter_upwards [Lp.coeFn_sub (leading c • (logBFirst c 0:Hq)) (burnolRieszSingleFourierSource c:Hq),
    Lp.coeFn_smul (leading c) (logBFirst c 0:Hq),log_read c,burnolRieszSingleFourierSource_ae_raw c]
    with x subtracted scaled log source
  change ((leading c • (logBFirst c 0:Hq)-(burnolRieszSingleFourierSource c:Hq):Hq) x)=_
  rw [subtracted,Pi.sub_apply,scaled,Pi.smul_apply,smul_eq_mul,log,source]

private theorem log_raw_local (c:BurnolCompletedMellinCoordinate):
    ContinuousOn (logRaw c) (Icc (q/2) q) := by
  have power:ContinuousOn (SingularCounting.powerRaw c) (Icc (q/2) q) := by
    intro x inside
    have positive:0<x := by linarith [inside.1]
    exact ((Complex.continuousAt_ofReal_cpow_const |x| (star c.value-1)
      (Or.inr (abs_ne_zero.mpr positive.ne'))).comp continuous_abs.continuousAt).continuousWithinAt
  exact (power.sub continuousOn_const).add (return_raw_continuous (S (logBFirst c 0))).continuousOn

/-- The endpoint is read from the canonical raw; the inverse construction pays its identity. -/
theorem native_beta_source (c:BurnolCompletedMellinCoordinate):
    nativeBeta c=leading c*logBeta c-Kernel.beta c := by
  have same:nativeRaw c=ᵐ[μq]fun x:ℝ=>leading c*logRaw c x-burnolRieszSingleFourierSourceRaw c x :=
    (native_read c).symm.trans (generated_native_read c)
  have restriction:nativeRaw c=ᵐ[volume.restrict (Icc (q/2) q)]
      fun x:ℝ=>leading c*logRaw c x-burnolRieszSingleFourierSourceRaw c x :=
    ae_restrict_of_ae_restrict_of_subset (show Icc (q/2) q ⊆ symmetricInterval q by
      intro x hx;constructor <;> linarith [hx.1,hx.2]) same
  have rawContinuous:Continuous (nativeRaw c) := actual_centered_continuous _ (actual_dual_integrable _ _)
  have bContinuous:ContinuousOn (burnolRieszSingleFourierSourceRaw c) (Icc (q/2) q) := by
    intro x inside
    exact (burnolRieszSingleFourierSourceRaw_continuousAt c (by linarith [inside.1])).continuousWithinAt
  have actual:=Measure.eqOn_Icc_of_ae_eq (μ:=(volume:Measure ℝ)) (by norm_num : (q/2:ℝ)≠q)
    restriction rawContinuous.continuousOn ((log_raw_local c).const_mul (leading c) |>.sub bContinuous)
    (show q∈Icc (q/2) q by constructor <;> norm_num)
  simpa only [nativeBeta,logRaw,logBeta,powerBeta,Kernel.beta] using actual

private theorem mean_raw_linear (scalar:ℂ) (left right:M) (x:ℝ):
    burnolMeanZeroFourierRaw (scalar • left-right) x=
      scalar*burnolMeanZeroFourierRaw left x-burnolMeanZeroFourierRaw right x := by
  have fourier:burnolRadiusTruncatedFourierRaw q (scalar • (left:Hq)-(right:Hq)) x=
      scalar*burnolRadiusTruncatedFourierRaw q (left:Hq) x-burnolRadiusTruncatedFourierRaw q (right:Hq) x := by
    rw [sub_eq_add_neg,←neg_one_smul ℂ (right:Hq),burnolRadiusTruncatedFourierRaw_add,
      burnolRadiusTruncatedFourierRaw_smul,burnolRadiusTruncatedFourierRaw_smul]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,neg_one_mul,sub_eq_add_neg]
  unfold burnolMeanZeroFourierRaw
  simp only [Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul]
  rw [fourier]
  unfold burnolQuarterMeanCoefficient
  rw [inner_sub_right,inner_smul_right]
  ring

theorem native_gamma_source (c:BurnolCompletedMellinCoordinate):
    nativeGamma c=leading c*logGamma c-burnolRieszReturnRaw c q :=
  mean_raw_linear (leading c) (logBFirst c 0) (burnolRieszSingleFourierSource c) q

/-- This value is generated by the actual native source, including the opposite original a term. -/
def nativeEuler (c:BurnolCompletedMellinCoordinate):M:=
  rate c • nativeSmooth c+(nativeGamma c-originCoefficient c) • Response.u-nativeBeta c • Response.v

private theorem native_euler_value (c:BurnolCompletedMellinCoordinate):
    leading c • logEuler c-Euler.sourceEuler c=nativeEuler c := by
  rw [log_euler,Euler.sourceEuler_eq]
  unfold nativeEuler
  rw [native_gamma_source,native_beta_source]
  unfold rate nativeSmooth originCoefficient Kernel.A
  module

/-- The complete canonical native raw generates its local Euler equation. -/
theorem native_euler (c:BurnolCompletedMellinCoordinate):
    GapEuler.euler (E (nativeSmooth c:Hq):TemperedDistribution ℝ ℂ)=
      (E (nativeEuler c:Hq):TemperedDistribution ℝ ℂ)-nativeBeta c • GapEuler.edge q := by
  have whole:(E (nativeSmooth c:Hq):TemperedDistribution ℝ ℂ)=
      leading c • (E (logBFirst c 0:Hq):TemperedDistribution ℝ ℂ)-
        (E (burnolRieszSingleFourierSource c:Hq):TemperedDistribution ℝ ℂ) := by
    simp only [nativeSmooth,Submodule.coe_sub,Submodule.coe_smul,
      ←Lp.toTemperedDistributionCLM_apply,map_sub,map_smul]
  rw [whole,map_sub,map_smul,log_weak,Euler.source_euler]
  rw [←native_euler_value,native_beta_source]
  simp only [Submodule.coe_sub,Submodule.coe_smul,←Lp.toTemperedDistributionCLM_apply,map_sub,map_smul]
  module

/-- The original centered edge contributes its half-mean term to the true L2 Euler field. -/
theorem native_corrected_euler (c:BurnolCompletedMellinCoordinate):
    GapEuler.euler ((E (nativeSmooth c:Hq)-nativeBeta c • C:BurnolL2):TemperedDistribution ℝ ℂ)=
      ((E (nativeEuler c:Hq)+(nativeBeta c/2) • C:BurnolL2):TemperedDistribution ℝ ℂ) := by
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 _)=
    Lp.toTemperedDistributionCLM ℂ volume 2 _
  simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  rw [native_euler,constant_euler]
  module

end OriginalCanonicalNativeEulerGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
