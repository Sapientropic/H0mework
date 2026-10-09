import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatLocalNativeWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatHamiltonianCoefficient
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiHeatLocalNativeGaussian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore ClockPhiConservativeHeatSource
open SourceClockPhiHeatHamiltonianCoefficient SourceClockPhiHeatLocalNativeWork SourceClockPhiCompleteHeatGainPayment
open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev gaussian:=gaussianReal 0 1
private abbrev config:=GaussHistoryHilbert.configurationMeasure
private def coefficient(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=heatMean t z+Real.sqrt (heatVariance t z)*ξ
private def profile(t p q ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=(forwardRatio t z)^p*Real.exp (q*coefficient t ξ z)
private theorem coefficient_smooth(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (coefficient t ξ) z.val:=by
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  have hL:0<heatLog t z.val:=Real.log_pos (by
    change 1<1+18*t*reciprocalVolume z.val
    have h:0<18*t*reciprocalVolume z.val:=by positivity
    linarith)
  have h:ContDiffAt ℝ ∞ (heatLog t) z.val:=by
    apply (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_const).mul (reciprocal_volume_smooth z))).log
    change 1+18*t*reciprocalVolume z.val≠0
    positivity
  exact ((h.neg).div_const 6).add
    (((h.div_const 9).sqrt (by exact ne_of_gt (div_pos hL (by norm_num)))).mul contDiffAt_const)
private theorem power_smooth(t:ℝ)(ht:0<t)(p:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(forwardRatio t x)^p) z.val:=by
  have h:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact h.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne'
private theorem profile_smooth(t:ℝ)(ht:0<t)(p q ξ:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (profile t p q ξ) z.val:=
  (power_smooth t ht p z).mul ((contDiffAt_const.mul (coefficient_smooth t ht ξ z)).exp)

def heatProfileWeight(t:ℝ)(ht:0<t)(p q ξ:ℝ):Op:=multiply (profile t p q ξ) (profile_smooth t ht p q ξ)
def gaussianProfileWeight(t:ℝ)(ht:0<t)(a:ℝ):Op:=multiply (fun z=>(forwardRatio t z)^a) (power_smooth t ht a)

private theorem density_multiply(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (f h:QuantumTest)(z:SourceCoordinateSlice):densityPair f (multiply b hb h) z=(b z:ℂ)*densityPair f h z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (f z word)*((b z:ℂ)*h z word)=_
  ring
private theorem density_offchart(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉physicalChart):densityPair f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun hx=>hz (f.tsupport_subset hx))
  simp only [densityPair,hf,map_zero,inner_zero_left]
private theorem exponential_moment(t:ℝ)(ht:0<t)(q:ℝ)(z:physicalChart):
    Integrable (fun ξ:ℝ=>Real.exp (q*coefficient t ξ z.val)) gaussian∧
      (∫ξ:ℝ,Real.exp (q*coefficient t ξ z.val) ∂gaussian)=(forwardRatio t z.val)^(q*(q-3)/18):=by
  have h:=actual_heat_exponential_moment (GaussNativeEnergy.volume z.val) t q (volume_pos z) ht
  have he:heatLog t z.val=Real.log ((GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val):=by
    unfold heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  simpa only [coefficient,heatMean,heatVariance,he,forwardRatio,Real.rpow_eq_pow] using h
private theorem power_measurable(p:ℝ):Measurable (fun x:ℝ=>x^p):=
  measurable_of_continuousOn_compl_singleton 0 (fun x hx=>
    (Real.continuousAt_rpow_const x p (.inl (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hx))).continuousWithinAt)
private theorem log_measurable:Measurable Real.log:=
  measurable_of_continuousOn_compl_singleton 0 (fun x hx=>
    (Real.continuousAt_log (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hx)).continuousWithinAt)
private theorem profile_measurable(t p q:ℝ):Measurable (fun x:SourceCoordinateSlice×ℝ=>profile t p q x.2 x.1):=by
  have hV:Measurable (fun x:SourceCoordinateSlice×ℝ=>GaussNativeEnergy.volume x.1):=volume_smooth.continuous.measurable.comp measurable_fst
  have hR:Measurable (fun x:SourceCoordinateSlice×ℝ=>forwardRatio t x.1):=(hV.add_const (18*t)).div hV
  have hL:Measurable (fun x:SourceCoordinateSlice×ℝ=>heatLog t x.1):=by
    exact log_measurable.comp (measurable_const.add (measurable_const.mul hV.inv))
  have hc:Measurable (fun x:SourceCoordinateSlice×ℝ=>coefficient t x.2 x.1):=
    (hL.neg.div_const 6).add ((Real.continuous_sqrt.measurable.comp (hL.div_const 9)).mul measurable_snd)
  exact ((power_measurable p).comp hR).mul (Real.continuous_exp.measurable.comp (measurable_const.mul hc))
private def kernel(t p q:ℝ)(f h:QuantumTest)(x:SourceCoordinateSlice×ℝ):ℂ:=
  (profile t p q x.2 x.1:ℂ)*densityPair f h x.1
private theorem kernel_section(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun ξ:ℝ=>kernel t p q f h (z,ξ)) gaussian:=by
  by_cases hz:z∈physicalChart
  · have hi:=((exponential_moment t ht q ⟨z,hz⟩).1.const_mul ((forwardRatio t z)^p)).ofReal.mul_const (densityPair f h z)
    convert! hi using 1
  · simp only [kernel,density_offchart f h z hz,mul_zero]
    exact integrable_const (0:ℂ)
private theorem kernel_integral(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫ξ:ℝ,kernel t p q f h (z,ξ) ∂gaussian)=densityPair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h) z:=by
  rw [gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hm:=(exponential_moment t ht q ⟨z,hz⟩).2
    simp only [kernel,profile,Complex.ofReal_mul]
    rw [integral_mul_const,integral_const_mul,integral_complex_ofReal,hm]
    rw [←Complex.ofReal_mul,←Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩)]
  · simp only [kernel,density_offchart f h z hz,mul_zero,integral_zero]
private theorem kernel_norm_integral(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫ξ:ℝ,‖kernel t p q f h (z,ξ)‖ ∂gaussian)=‖densityPair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h) z‖:=by
  rw [gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hpos:∀ξ:ℝ,0≤profile t p q ξ z:=fun ξ=>mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
    have hm:=(exponential_moment t ht q ⟨z,hz⟩).2
    simp only [kernel,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (hpos _)]
    dsimp only [profile]
    rw [integral_mul_const,integral_const_mul,hm]
    rw [←Real.rpow_add hr]
    rw [abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  · simp only [kernel,density_offchart f h z hz,mul_zero,norm_zero,integral_zero]

theorem actual_gaussian_weighted_source_pair(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair f (heatProfileWeight t ht p q ξ h)) gaussian∧
      (∫ξ:ℝ,sourcePair f (heatProfileWeight t ht p q ξ h) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h):=by
  have hm:AEStronglyMeasurable (kernel t p q f h) (config.prod gaussian):=
    (Complex.continuous_ofReal.measurable.comp (profile_measurable t p q)).aestronglyMeasurable.mul
      (densityPair_integrable f h).aestronglyMeasurable.comp_fst
  have hp:Integrable (kernel t p q f h) (config.prod gaussian):=by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Filter.Eventually.of_forall (kernel_section t ht p q f h)
    · exact (densityPair_integrable f (gaussianProfileWeight t ht (p+q*(q-3)/18) h)).norm.congr
        (Filter.Eventually.of_forall (fun z=>(kernel_norm_integral t ht p q f h z).symm))
  have he(ξ:ℝ):sourcePair f (heatProfileWeight t ht p q ξ h)=∫z,kernel t p q f h (z,ξ) ∂config:=by
    rw [sourcePair_integral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z=>density_multiply _ _ f h z)
  refine ⟨hp.integral_prod_right.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  have hs:Integrable (Function.uncurry (fun z ξ=>kernel t p q f h (z,ξ))) (config.prod gaussian):=hp
  rw [←integral_integral_swap hs]
  simp_rw [kernel_integral t ht p q f h]
  exact (sourcePair_integral _ _).symm

private theorem heat_matter_reader(t:ℝ)(ht:0<t)(ξ:ℝ):
    heatProfileWeight t ht 0 1 ξ=multiply (fun z=>Real.exp (heatMean t z+Real.sqrt (heatVariance t z)*ξ))
      (fun z=>(coefficient_smooth t ht ξ z).exp):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (profile t 0 1 ξ z:ℂ) • f z=(Real.exp (coefficient t ξ z):ℂ) • f z
  unfold profile
  rw [Real.rpow_zero,one_mul,one_mul]
private theorem heat_zero_reader(t:ℝ)(ht:0<t)(p ξ:ℝ):
    heatProfileWeight t ht p 0 ξ=gaussianProfileWeight t ht p:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (profile t p 0 ξ z:ℂ) • f z=(((forwardRatio t z)^p:ℝ):ℂ) • f z
  unfold profile
  rw [zero_mul,Real.exp_zero,mul_one]
attribute [local irreducible] completeHeatCore GaussMatterCore.matterAction
  SourceScalarVirialBulk.centeredAction SourceScalarVirialBulk.vacuumLinearAction
  SourceScalarVirialBulk.vacuumConstantAction SourceScalarVirialBulk.scalarSpatialAction SourceScalarVirialBulk.magneticAction

theorem actual_complete_matter_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (0) (1) f (GaussMatterCore.matterAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (GaussMatterCore.matterAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (0) (1) ξ (GaussMatterCore.matterAction g)):=by
    rw [actual_complete_matter_pair]
    rw [heat_matter_reader]
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (0:ℝ)+(1)*((1)-3)/18=-1/9 by norm_num]

theorem actual_complete_centered_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.centeredAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.centeredAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (17/9) (SourceScalarVirialBulk.centeredAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (4/3) (-2) f (SourceScalarVirialBulk.centeredAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.centeredAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (4/3) (-2) ξ (SourceScalarVirialBulk.centeredAction g)):=by
    rw [actual_complete_centered_pair]
    rfl
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (4/3:ℝ)+(-2)*((-2)-3)/18=17/9 by norm_num]

theorem actual_complete_vacuum_linear_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumLinearAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumLinearAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (14/9) (SourceScalarVirialBulk.vacuumLinearAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (4/3) (-1) f (SourceScalarVirialBulk.vacuumLinearAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumLinearAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (4/3) (-1) ξ (SourceScalarVirialBulk.vacuumLinearAction g)):=by
    rw [actual_complete_vacuum_linear_pair]
    rfl
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (4/3:ℝ)+(-1)*((-1)-3)/18=14/9 by norm_num]

theorem actual_complete_vacuum_constant_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumConstantAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumConstantAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (12/9) (SourceScalarVirialBulk.vacuumConstantAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (4/3) (0) f (SourceScalarVirialBulk.vacuumConstantAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.vacuumConstantAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (4/3) (0) ξ (SourceScalarVirialBulk.vacuumConstantAction g)):=by
    rw [actual_complete_vacuum_constant_pair]
    rw [heat_zero_reader]
    rfl
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (4/3:ℝ)+(0)*((0)-3)/18=12/9 by norm_num]

theorem actual_complete_signed_spatial_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.scalarSpatialAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.scalarSpatialAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (6/9) (SourceScalarVirialBulk.scalarSpatialAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (2/3) (0) f (SourceScalarVirialBulk.scalarSpatialAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.scalarSpatialAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (2/3) (0) ξ (SourceScalarVirialBulk.scalarSpatialAction g)):=by
    rw [actual_complete_signed_spatial_pair]
    rw [heat_zero_reader]
    rfl
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (2/3:ℝ)+(0)*((0)-3)/18=6/9 by norm_num]

theorem actual_complete_magnetic_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.magneticAction (completeHeatCore t ht ξ g))) gaussian∧
      (∫ξ:ℝ,sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.magneticAction (completeHeatCore t ht ξ g)) ∂gaussian)=
        sourcePair f (gaussianProfileWeight t ht (8/9) (SourceScalarVirialBulk.magneticAction g)):=by
  have h:=actual_gaussian_weighted_source_pair t ht (2/3) (4) f (SourceScalarVirialBulk.magneticAction g)
  have he(ξ:ℝ):sourcePair (completeHeatCore t ht ξ f) (SourceScalarVirialBulk.magneticAction (completeHeatCore t ht ξ g))=
      sourcePair f (heatProfileWeight t ht (2/3) (4) ξ (SourceScalarVirialBulk.magneticAction g)):=by
    rw [actual_complete_magnetic_pair]
    rfl
  refine ⟨h.1.congr (Filter.Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  rw [h.2]
  rw [show (2/3:ℝ)+(4)*((4)-3)/18=8/9 by norm_num]
end LowEnergy.SourceClockPhiHeatLocalNativeGaussian
