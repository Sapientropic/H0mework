import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatHamiltonianSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedCovarianceInfinitesimal
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatRadialCovariancePair
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0FirstJet
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatComparisonWork ClockPhiCorrectedCovarianceInfinitesimal ClockPhiConservativeHeatSource
open ClockPhiHeatRadialCovariancePair ClockPhiHeatCoframeHamiltonianWork SourceClockPhiCombinedScalePressure
open SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceScalarVirialBulk
open SourceClockPhiCompleteHeatHamiltonianSource
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
private theorem ratio_power_hasDerivAt(a:ℝ)(z:physicalChart):
    HasDerivAt (fun t:ℝ=>(forwardRatio t z.val)^a)
      (18*a*reciprocalVolume z.val) 0:=by
  have he(t:ℝ):forwardRatio t z.val=1+18*t*reciprocalVolume z.val:=by
    unfold forwardRatio reciprocalVolume
    field_simp [(volume_pos z).ne']
  have hb:HasDerivAt (fun t:ℝ=>1+18*t*reciprocalVolume z.val)
      (18*reciprocalVolume z.val) 0:=by
    have heq:(fun t:ℝ=>1+18*t*reciprocalVolume z.val)=
        (fun t:ℝ=>1+(18*reciprocalVolume z.val)*t):=by funext t;ring
    rw [heq]
    simpa only [id_eq,mul_one] using ((hasDerivAt_id (0:ℝ)).const_mul (18*reciprocalVolume z.val)).const_add 1
  have hr:=hb.rpow_const (p:=a) (Or.inl (by norm_num:(1+18*(0:ℝ)*reciprocalVolume z.val)≠0))
  simp_rw [he]
  convert hr using 1
  simp only [zero_mul,mul_zero,add_zero,Real.one_rpow]
  ring
private theorem ratio_power_slope(a:ℝ)(z:physicalChart):
    Tendsto (fun t:ℝ=>((forwardRatio t z.val)^a-1)/t)
      (𝓝[>] (0:ℝ)) (𝓝 (18*a*reciprocalVolume z.val)):=by
  have h:= (ratio_power_hasDerivAt a z).tendsto_slope_zero_right
  have hz:forwardRatio 0 z.val=1:=by
    unfold forwardRatio
    norm_num
    exact (volume_pos z).ne'
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add,hz,Real.one_rpow,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]

private theorem ratio_power_deriv (a:ℝ) (s:ℝ) (z:physicalChart) (hs:0 ≤ s) :
    HasDerivAt (fun t:ℝ=>(forwardRatio t z.val)^a)
      ((18*reciprocalVolume z.val)*a*(forwardRatio s z.val)^(a-1)) s:=by
  have he(t:ℝ):forwardRatio t z.val=1+18*t*reciprocalVolume z.val:=by
    unfold forwardRatio reciprocalVolume
    field_simp [(volume_pos z).ne']
  have heq:(fun t:ℝ=>1+18*t*reciprocalVolume z.val)=
      (fun t:ℝ=>1+(18*reciprocalVolume z.val)*t):=by funext t;ring
  have hb:HasDerivAt (fun t:ℝ=>1+18*t*reciprocalVolume z.val)
      (18*reciprocalVolume z.val) s:=by
    rw [heq]
    simpa only [id_eq,mul_one] using ((hasDerivAt_id s).const_mul (18*reciprocalVolume z.val)).const_add 1
  have hr:=hb.rpow_const (p:=a) (Or.inl (ne_of_gt (by simpa only [←he] using forward_ratio_pos s hs z)))
  simp_rw [he]
  exact hr
private def derivativeWeight(a:ℝ)(p:ℝ×SourceCoordinateSlice):ℝ:=
  (18*reciprocalVolume p.2)*a*(forwardRatio p.1 p.2)^(a-1)
private theorem derivativeWeight_continuous(a:ℝ)(p:ℝ×SourceCoordinateSlice)
    (ht:0≤p.1)(hz:p.2∈physicalChart):ContinuousAt (derivativeWeight a) p:=by
  have hV:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>volume x.2) p:=
    volume_smooth.continuous.continuousAt.comp continuousAt_snd
  have hU:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>reciprocalVolume x.2) p:=by
    change ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>(volume x.2)⁻¹) p
    exact hV.inv₀ (volume_pos ⟨p.2,hz⟩).ne'
  have hR:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>forwardRatio x.1 x.2) p:=by
    change ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>(volume x.2+18*x.1)/volume x.2) p
    exact (hV.add (continuousAt_const.mul continuousAt_fst)).div hV (volume_pos ⟨p.2,hz⟩).ne'
  have hp:0<forwardRatio p.1 p.2:=forward_ratio_pos p.1 ht ⟨p.2,hz⟩
  exact ((continuousAt_const.mul hU).mul continuousAt_const).mul
    (hR.rpow_const (Or.inl hp.ne'))
private theorem derivativeWeight_bound(a:ℝ)(f:QuantumTest):
    ∃C:ℝ,0≤C ∧ ∀t∈Icc (0:ℝ) 1,∀z∈tsupport f,
      |derivativeWeight a (t,z)|≤C:=by
  have hc:ContinuousOn (derivativeWeight a) (Icc (0:ℝ) 1×ˢtsupport f):=by
    intro p hp
    exact (derivativeWeight_continuous a p hp.1.1 (f.tsupport_subset hp.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod f.hasCompactSupport).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht z hz
  simpa only [Real.norm_eq_abs] using ((hC (t,z) ⟨ht,hz⟩).trans (le_max_left C 0))
private theorem ratio_power_slope_bound(a:ℝ)(f:QuantumTest)(C:ℝ)
    (hC:∀t∈Icc (0:ℝ) 1,∀z∈tsupport f,|derivativeWeight a (t,z)|≤C)
    (t:ℝ)(ht:t∈Ioc (0:ℝ) 1)(z:SourceCoordinateSlice)(hz:z∈tsupport f):
    |((forwardRatio t z)^a-1)/t|≤C:=by
  have hzchart:z∈physicalChart:=f.tsupport_subset hz
  let zc:physicalChart:=⟨z,hzchart⟩
  have hbase:∀s∈Icc (0:ℝ) t,HasDerivAt (fun u:ℝ=>(forwardRatio u z)^a)
      (derivativeWeight a (s,z)) s:=by
    intro s hs
    exact ratio_power_deriv a s zc hs.1
  have hcont:ContinuousOn (fun u:ℝ=>(forwardRatio u z)^a) (Icc (0:ℝ) t):=
    fun s hs=>(hbase s hs).continuousAt.continuousWithinAt
  have hder:∀s∈Ico (0:ℝ) t,HasDerivWithinAt (fun u:ℝ=>(forwardRatio u z)^a)
      (derivativeWeight a (s,z)) (Ici s) s:=by
    intro s hs
    exact (hbase s (Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hb:∀s∈Ico (0:ℝ) t,‖derivativeWeight a (s,z)‖≤C:=by
    intro s hs
    rw [Real.norm_eq_abs]
    exact hC s ⟨hs.1,le_trans hs.2.le ht.2⟩ z hz
  have hm:=norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hb t ⟨ht.1.le,le_rfl⟩
  have hzero:forwardRatio 0 z=1:=by
    unfold forwardRatio
    norm_num
    exact (volume_pos zc).ne'
  simp only [hzero,Real.one_rpow,sub_zero,Real.norm_eq_abs] at hm
  have htn:t≠0:=ht.1.ne'
  rw [div_eq_mul_inv,abs_mul,abs_inv,abs_of_pos ht.1]
  have hdiv:=mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr ht.1.le)
  simpa only [mul_assoc,mul_inv_cancel₀ htn,mul_one] using hdiv

private theorem density_multiply(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (f h:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (multiply b hb h) z=(b z:ℂ)*densityPair f h z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (f z word)*((b z:ℂ)*h z word)=_
  ring
private def weightedKernel(a t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):ℂ:=
  if ht:0<t then (t:ℂ)⁻¹*(densityPair f (gaussianProfileWeight t ht a h) z-densityPair f h z) else 0
private theorem weightedKernel_point(a t:ℝ)(ht:0<t)(f h:QuantumTest)(z:physicalChart):
    weightedKernel a t f h z.val=((((forwardRatio t z.val)^a-1)/t:ℝ):ℂ)*densityPair f h z.val:=by
  unfold weightedKernel
  rw [dif_pos ht]
  change (t:ℂ)⁻¹*(densityPair f (multiply (fun y:SourceCoordinateSlice=>(forwardRatio t y)^a) _ h) z.val-
    densityPair f h z.val)=_
  rw [density_multiply]
  push_cast
  ring
private theorem weightedKernel_zero(a t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉tsupport f):
    weightedKernel a t f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport hz
  unfold weightedKernel
  split_ifs <;> simp [densityPair,hf]
private theorem weightedKernel_integrable(a t:ℝ)(f h:QuantumTest):
    Integrable (weightedKernel a t f h) GaussHistoryHilbert.configurationMeasure:=by
  by_cases ht:0<t
  · apply (((densityPair_integrable f (gaussianProfileWeight t ht a h)).sub (densityPair_integrable f h)).const_mul (t:ℂ)⁻¹).congr
    exact Eventually.of_forall (fun z=>by simp only [weightedKernel,dif_pos ht,Pi.sub_apply])
  · apply (integrable_zero SourceCoordinateSlice ℂ GaussHistoryHilbert.configurationMeasure).congr
    exact Eventually.of_forall (fun z=>by simp only [Pi.zero_apply,weightedKernel,dif_neg ht])
private theorem weightedKernel_limit(a:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    Tendsto (fun t:ℝ=>weightedKernel a t f h z) (𝓝[>] (0:ℝ))
      (𝓝 (((18*a*reciprocalVolume z:ℝ):ℂ)*densityPair f h z)):=by
  by_cases hz:z∈physicalChart
  · have hr:=ratio_power_slope a ⟨z,hz⟩
    have hh:=((Complex.continuous_ofReal.continuousAt.tendsto).comp hr).mul_const (densityPair f h z)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (weightedKernel_point a t ht f h ⟨z,hz⟩).symm
  · have hs:z∉tsupport f:=fun h=>hz (f.tsupport_subset h)
    have hf:f z=0:=image_eq_zero_of_notMem_tsupport hs
    simp only [weightedKernel_zero _ _ f h z hs,densityPair,hf,map_zero,inner_zero_left,mul_zero]
    exact tendsto_const_nhds
private theorem weightedKernel_integral(a t:ℝ)(f h:QuantumTest):
    (∫z,weightedKernel a t f h z ∂GaussHistoryHilbert.configurationMeasure)=
      if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht a h)-sourcePair f h) else 0:=by
  by_cases ht:0<t
  · simp only [weightedKernel,dif_pos ht]
    rw [integral_const_mul,integral_sub (densityPair_integrable f (gaussianProfileWeight t ht a h))
      (densityPair_integrable f h),←sourcePair_integral,←sourcePair_integral]
  · simp only [weightedKernel,dif_neg ht,integral_zero]

theorem actual_gaussian_weighted_source_pair_first_jet(a:ℝ)(f h:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (sourcePair f (gaussianProfileWeight t ht a h)-sourcePair f h) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 ((18*a:ℂ)*sourcePair f (inverseVolumeAction h))):=by
  obtain ⟨C,hC,hbound⟩:=derivativeWeight_bound a f
  have hdom:∀ᶠ t:ℝ in 𝓝[>] 0,∀ᵐ z ∂GaussHistoryHilbert.configurationMeasure,
      ‖weightedKernel a t f h z‖≤C*‖densityPair f h z‖:=by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num:(0:ℝ)<1)] with t ht
    exact Eventually.of_forall (fun z=>by
      by_cases hz:z∈tsupport f
      · rw [weightedKernel_point a t ht.1 f h ⟨z,f.tsupport_subset hz⟩,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (ratio_power_slope_bound a f C hbound t ht z hz) (norm_nonneg _)
      · rw [weightedKernel_zero a t f h z hz,norm_zero]
        positivity)
  have hh:=tendsto_integral_filter_of_dominated_convergence
    (μ:=GaussHistoryHilbert.configurationMeasure) (F:=fun t z=>weightedKernel a t f h z)
    (f:=fun z:SourceCoordinateSlice=>((18*a*reciprocalVolume z:ℝ):ℂ)*densityPair f h z)
    (fun z=>C*‖densityPair f h z‖)
    (Eventually.of_forall (fun t=>(weightedKernel_integrable a t f h).aestronglyMeasurable)) hdom
    ((densityPair_integrable f h).norm.const_mul C)
    (Eventually.of_forall (fun z=>weightedKernel_limit a f h z))
  have htarget:(∫z:SourceCoordinateSlice,((18*a*reciprocalVolume z:ℝ):ℂ)*densityPair f h z
      ∂GaussHistoryHilbert.configurationMeasure)=(18*a:ℂ)*sourcePair f (inverseVolumeAction h):=by
    have hi(z:SourceCoordinateSlice):densityPair f (inverseVolumeAction h) z=
        (reciprocalVolume z:ℂ)*densityPair f h z:=density_multiply _ _ f h z
    have he(z:SourceCoordinateSlice):((18*a*reciprocalVolume z:ℝ):ℂ)*densityPair f h z=
        (18*a:ℂ)*densityPair f (inverseVolumeAction h) z:=by
      rw [hi]
      push_cast
      ring
    simp_rw [he]
    rw [integral_const_mul,←sourcePair_integral]
  simpa only [weightedKernel_integral,htarget] using hh

private def squareGap(V t:ℝ):ℝ:=(1/V)^2-(1/(V+18*t))^2
private theorem squareGap_ratio(V t:ℝ)(hV:0<V)(ht:0<t):
    squareGap V t/t=36*(V+9*t)/(V^2*(V+18*t)^2):=by
  unfold squareGap
  have hW:V+18*t≠0:=by positivity
  field_simp [hV.ne',ht.ne',hW]
  ring
private theorem squareGap_ratio_limit(V:ℝ)(hV:0<V):
    Tendsto (fun t:ℝ=>squareGap V t/t) (𝓝[>] (0:ℝ)) (𝓝 (36/V^3)):=by
  have hc:ContinuousAt (fun t:ℝ=>36*(V+9*t)/(V^2*(V+18*t)^2)) 0:=by
    fun_prop (disch:=positivity)
  have hh:Tendsto (fun t:ℝ=>36*(V+9*t)/(V^2*(V+18*t)^2)) (𝓝[>] (0:ℝ))
      (𝓝 (36*(V+9*(0:ℝ))/(V^2*(V+18*0)^2))):=hc.tendsto.mono_left nhdsWithin_le_nhds
  have hv:36*(V+9*(0:ℝ))/(V^2*(V+18*0)^2)=36/V^3:=by
    field_simp [hV.ne']
    ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (squareGap_ratio V t hV ht).symm
private theorem clockKappa_square_ratio_limit(V:ℝ)(hV:0<V):
    Tendsto (fun t:ℝ=>(((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t)
      (𝓝[>] (0:ℝ)) (𝓝 (18/V^3)):=by
  have hq:=squareGap_ratio_limit V hV
  have hg:=actual_clock_covariance_first_order_zero V hV
  have h:=((hq.sub hg).div_const 2)
  have hv:(36/V^3-0)/2=18/V^3:=by ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (squareGap V t/t-(squareGap V t-
    2*((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t)/2=_
  have ht':0<t:=ht
  field_simp [ht'.ne']
  ring
theorem actual_heat_kappa_square_first_jet(z:physicalChart):
    Tendsto (fun t:ℝ=>(heatKappa t z.val)^2/t) (𝓝[>] (0:ℝ))
      (𝓝 (18*(reciprocalVolume z.val)^3)):=by
  have h:=clockKappa_square_ratio_limit (volume z.val) (volume_pos z)
  have he(t:ℝ):heatLog t z.val=Real.log ((volume z.val+18*t)/volume z.val):=by
    unfold heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  have hv:18*(reciprocalVolume z.val)^3=18/(volume z.val)^3:=by
    unfold reciprocalVolume
    field_simp [(volume_pos z).ne']
  rw [hv]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  unfold heatKappa SourceClockPhiForwardNativeReturn.forwardU reciprocalVolume
  rw [he]
  simp only [one_div]

private theorem squareGap_ratio_bound(V t:ℝ)(hV:0<V)(ht:0<t):
    squareGap V t/t≤36/V^3:=by
  rw [squareGap_ratio V t hV ht]
  have hW:0<V+18*t:=by positivity
  have hd:0<V^2*(V+18*t)^2:=by positivity
  have hv:0<V^3:=pow_pos hV 3
  apply (div_le_div_iff₀ hd hv).mpr
  nlinarith [sq_nonneg t, mul_pos hV ht, sq_nonneg (V+18*t)]
private theorem clockKappa_square_ratio_bound(V t:ℝ)(hV:0<V)(ht:0<t):
    0≤(((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t ∧
      (((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t≤18/V^3:=by
  have hp:=SourceClockPhiHeatComparisonPrice.clock_comparison_price V t hV ht
  have hq:(((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2) ≤ squareGap V t/2:=by
    unfold squareGap
    linarith
  constructor
  · exact div_nonneg (sq_nonneg _) ht.le
  · have hdiv:(((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2)/t≤
        (squareGap V t/t)/2:=by
      apply (div_le_iff₀ ht).mpr
      have he:(squareGap V t/t/2)*t=squareGap V t/2:=by field_simp [ht.ne']
      rw [he]
      exact hq
    calc
      _ ≤ squareGap V t/t/2 := hdiv
      _ ≤ (36/V^3)/2 := div_le_div_of_nonneg_right (squareGap_ratio_bound V t hV ht) (by norm_num)
      _ = 18/V^3 := by ring
private theorem heatKappa_square_price(t:ℝ)(ht:0<t)(z:physicalChart):
    0≤(heatKappa t z.val)^2/t ∧
      (heatKappa t z.val)^2/t≤18*(reciprocalVolume z.val)^3:=by
  have hp:=clockKappa_square_ratio_bound (volume z.val) t (volume_pos z) ht
  have he:heatLog t z.val=Real.log ((volume z.val+18*t)/volume z.val):=by
    unfold heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  have hv:18*(reciprocalVolume z.val)^3=18/(volume z.val)^3:=by
    unfold reciprocalVolume
    field_simp [(volume_pos z).ne']
  rw [hv]
  convert hp using 1 <;>
    simp only [heatKappa,SourceClockPhiForwardNativeReturn.forwardU,reciprocalVolume,he,one_div]

private theorem kappa_density(t:ℝ)(ht:0<t)(f h:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (kappaAction t ht (kappaAction t ht h)) z=
      ((heatKappa t z)^2:ℂ)*densityPair f h z:=by
  change densityPair f (multiply (heatKappa t) _ (multiply (heatKappa t) _ h)) z=_
  rw [density_multiply,density_multiply]
  ring
private theorem inverse_cube_density(f h:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))) z=
      ((reciprocalVolume z)^3:ℂ)*densityPair f h z:=by
  change densityPair f (multiply reciprocalVolume _ (multiply reciprocalVolume _
    (multiply reciprocalVolume _ h))) z=_
  rw [density_multiply,density_multiply,density_multiply]
  ring
private def kappaKernel(t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):ℂ:=
  if ht:0<t then (t:ℂ)⁻¹*densityPair f (kappaAction t ht (kappaAction t ht h)) z else 0
private theorem kappaKernel_point(t:ℝ)(ht:0<t)(f h:QuantumTest)(z:physicalChart):
    kappaKernel t f h z.val=(((heatKappa t z.val)^2/t:ℝ):ℂ)*densityPair f h z.val:=by
  unfold kappaKernel
  rw [dif_pos ht,kappa_density]
  push_cast
  ring
private theorem kappaKernel_zero(t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉tsupport f):
    kappaKernel t f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport hz
  unfold kappaKernel
  split_ifs <;> simp [densityPair,hf]
private theorem kappaKernel_integrable(t:ℝ)(f h:QuantumTest):
    Integrable (kappaKernel t f h) GaussHistoryHilbert.configurationMeasure:=by
  by_cases ht:0<t
  · apply ((densityPair_integrable f (kappaAction t ht (kappaAction t ht h))).const_mul (t:ℂ)⁻¹).congr
    exact Eventually.of_forall (fun z=>by simp only [kappaKernel,dif_pos ht])
  · apply (integrable_zero SourceCoordinateSlice ℂ GaussHistoryHilbert.configurationMeasure).congr
    exact Eventually.of_forall (fun z=>by simp only [Pi.zero_apply,kappaKernel,dif_neg ht])
private theorem kappaKernel_limit(f h:QuantumTest)(z:SourceCoordinateSlice):
    Tendsto (fun t:ℝ=>kappaKernel t f h z) (𝓝[>] (0:ℝ))
      (𝓝 (((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z)):=by
  by_cases hz:z∈physicalChart
  · have hr:=actual_heat_kappa_square_first_jet ⟨z,hz⟩
    have hh:=((Complex.continuous_ofReal.continuousAt.tendsto).comp hr).mul_const (densityPair f h z)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (kappaKernel_point t ht f h ⟨z,hz⟩).symm
  · have hs:z∉tsupport f:=fun h=>hz (f.tsupport_subset h)
    have hf:f z=0:=image_eq_zero_of_notMem_tsupport hs
    simp only [kappaKernel_zero _ f h z hs,densityPair,hf,map_zero,inner_zero_left,mul_zero]
    exact tendsto_const_nhds
private theorem kappaKernel_integral(t:ℝ)(f h:QuantumTest):
    (∫z,kappaKernel t f h z ∂GaussHistoryHilbert.configurationMeasure)=
      if ht:0<t then (t:ℂ)⁻¹*sourcePair f (kappaAction t ht (kappaAction t ht h)) else 0:=by
  by_cases ht:0<t
  · simp only [kappaKernel,dif_pos ht]
    rw [integral_const_mul,←sourcePair_integral]
  · simp only [kappaKernel,dif_neg ht,integral_zero]

theorem actual_heat_kappa_square_source_pair_first_jet(f h:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      sourcePair f (kappaAction t ht (kappaAction t ht h)) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((18:ℂ)*sourcePair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))))):=by
  let h3:=inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))
  have hdom:∀ᶠ t:ℝ in 𝓝[>] 0,∀ᵐ z ∂GaussHistoryHilbert.configurationMeasure,
      ‖kappaKernel t f h z‖≤18*‖densityPair f h3 z‖:=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall (fun z=>by
      by_cases hz:z∈tsupport f
      · let zc:physicalChart:=⟨z,f.tsupport_subset hz⟩
        have hp:=heatKappa_square_price t ht zc
        have hu:0≤reciprocalVolume z:=le_of_lt (inv_pos.mpr (volume_pos zc))
        have hd:‖densityPair f h3 z‖=(reciprocalVolume z)^3*‖densityPair f h z‖:=by
          change ‖densityPair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))) z‖=_
          rw [inverse_cube_density,norm_mul,←Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hu 3)]
        rw [kappaKernel_point t ht f h zc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hp.1,hd]
        calc
          _ ≤ (18*(reciprocalVolume z)^3)*‖densityPair f h z‖ :=
            mul_le_mul_of_nonneg_right hp.2 (norm_nonneg _)
          _ = 18*((reciprocalVolume z)^3*‖densityPair f h z‖) := by ring
      · rw [kappaKernel_zero t f h z hz,norm_zero]
        positivity)
  have hh:=tendsto_integral_filter_of_dominated_convergence
    (μ:=GaussHistoryHilbert.configurationMeasure) (F:=fun t z=>kappaKernel t f h z)
    (f:=fun z:SourceCoordinateSlice=>((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z)
    (fun z=>18*‖densityPair f h3 z‖)
    (Eventually.of_forall (fun t=>(kappaKernel_integrable t f h).aestronglyMeasurable)) hdom
    ((densityPair_integrable f h3).norm.const_mul 18)
    (Eventually.of_forall (fun z=>kappaKernel_limit f h z))
  have htarget:(∫z:SourceCoordinateSlice,((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z
      ∂GaussHistoryHilbert.configurationMeasure)=(18:ℂ)*sourcePair f h3:=by
    have he(z:SourceCoordinateSlice):((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z=
        (18:ℂ)*densityPair f h3 z:=by
      change _=(18:ℂ)*densityPair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))) z
      rw [inverse_cube_density]
      push_cast
      ring
    simp_rw [he]
    rw [integral_const_mul,←sourcePair_integral]
  simpa only [kappaKernel_integral,htarget,h3] using hh

private theorem weighted_kappa_density(a t:ℝ)(ht:0<t)(f h:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (kappaAction t ht (gaussianProfileWeight t ht a (kappaAction t ht h))) z=
      ((((heatKappa t z)^2*(forwardRatio t z)^a):ℝ):ℂ)*densityPair f h z:=by
  change densityPair f (multiply (heatKappa t) _
    (multiply (fun y:SourceCoordinateSlice=>(forwardRatio t y)^a) _ (multiply (heatKappa t) _ h))) z=_
  rw [density_multiply,density_multiply,density_multiply]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  ring
private def weightedKappaKernel(a t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):ℂ:=
  if ht:0<t then (t:ℂ)⁻¹*densityPair f
    (kappaAction t ht (gaussianProfileWeight t ht a (kappaAction t ht h))) z else 0
private theorem weightedKappaKernel_point(a t:ℝ)(ht:0<t)(f h:QuantumTest)(z:physicalChart):
    weightedKappaKernel a t f h z.val=
      ((((heatKappa t z.val)^2/t)*(forwardRatio t z.val)^a:ℝ):ℂ)*densityPair f h z.val:=by
  unfold weightedKappaKernel
  rw [dif_pos ht,weighted_kappa_density]
  push_cast
  ring
private theorem weightedKappaKernel_zero(a t:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉tsupport f):
    weightedKappaKernel a t f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport hz
  unfold weightedKappaKernel
  split_ifs <;> simp [densityPair,hf]
private theorem weightedKappaKernel_integrable(a t:ℝ)(f h:QuantumTest):
    Integrable (weightedKappaKernel a t f h) GaussHistoryHilbert.configurationMeasure:=by
  by_cases ht:0<t
  · apply ((densityPair_integrable f (kappaAction t ht (gaussianProfileWeight t ht a (kappaAction t ht h)))).const_mul (t:ℂ)⁻¹).congr
    exact Eventually.of_forall (fun z=>by simp only [weightedKappaKernel,dif_pos ht])
  · apply (integrable_zero SourceCoordinateSlice ℂ GaussHistoryHilbert.configurationMeasure).congr
    exact Eventually.of_forall (fun z=>by simp only [Pi.zero_apply,weightedKappaKernel,dif_neg ht])
private theorem weightedKappaKernel_limit(a:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    Tendsto (fun t:ℝ=>weightedKappaKernel a t f h z) (𝓝[>] (0:ℝ))
      (𝓝 (((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z)):=by
  by_cases hz:z∈physicalChart
  · have hk:=actual_heat_kappa_square_first_jet ⟨z,hz⟩
    have hw:Tendsto (fun t:ℝ=>(forwardRatio t z)^a) (𝓝[>] (0:ℝ)) (𝓝 1):=by
      have hc:ContinuousAt (fun t:ℝ=>(forwardRatio t z)^a) 0:=
        (ratio_power_hasDerivAt a ⟨z,hz⟩).continuousAt
      have hzero:forwardRatio 0 z=1:=by
        unfold forwardRatio
        norm_num
        exact (volume_pos ⟨z,hz⟩).ne'
      simpa only [hzero,Real.one_rpow] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hh:=((Complex.continuous_ofReal.continuousAt.tendsto).comp (hk.mul hw)).mul_const (densityPair f h z)
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (weightedKappaKernel_point a t ht f h ⟨z,hz⟩).symm
  · have hs:z∉tsupport f:=fun h=>hz (f.tsupport_subset h)
    have hf:f z=0:=image_eq_zero_of_notMem_tsupport hs
    simp only [weightedKappaKernel_zero _ _ f h z hs,densityPair,hf,map_zero,inner_zero_left,mul_zero]
    exact tendsto_const_nhds
private theorem weightedKappaKernel_integral(a t:ℝ)(f h:QuantumTest):
    (∫z,weightedKappaKernel a t f h z ∂GaussHistoryHilbert.configurationMeasure)=
      if ht:0<t then (t:ℂ)⁻¹*sourcePair f
        (kappaAction t ht (gaussianProfileWeight t ht a (kappaAction t ht h))) else 0:=by
  by_cases ht:0<t
  · simp only [weightedKappaKernel,dif_pos ht]
    rw [integral_const_mul,←sourcePair_integral]
  · simp only [weightedKappaKernel,dif_neg ht,integral_zero]

theorem actual_heat_weighted_kappa_square_source_pair_first_jet(a:ℝ)(f h:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*sourcePair f
      (kappaAction t ht (gaussianProfileWeight t ht a (kappaAction t ht h))) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((18:ℂ)*sourcePair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))))):=by
  let h3:=inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))
  obtain ⟨C,hC,hbound⟩:=derivativeWeight_bound a f
  have hdom:∀ᶠ t:ℝ in 𝓝[>] 0,∀ᵐ z ∂GaussHistoryHilbert.configurationMeasure,
      ‖weightedKappaKernel a t f h z‖≤18*(1+C)*‖densityPair f h3 z‖:=by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num:(0:ℝ)<1)] with t ht
    exact Eventually.of_forall (fun z=>by
      by_cases hz:z∈tsupport f
      · let zc:physicalChart:=⟨z,f.tsupport_subset hz⟩
        have hp:=heatKappa_square_price t ht.1 zc
        have hu:0≤reciprocalVolume z:=le_of_lt (inv_pos.mpr (volume_pos zc))
        have hs:=ratio_power_slope_bound a f C hbound t ht z hz
        have hc:(forwardRatio t z)^a≤1+C:=by
          have hle:((forwardRatio t z)^a-1)/t≤C:=(le_abs_self _).trans hs
          have hh:((forwardRatio t z)^a-1)≤C*t:=(div_le_iff₀ ht.1).mp hle
          have hct:C*t≤C:=by nlinarith [hC,ht.2]
          linarith
        have hr:0≤(forwardRatio t z)^a:=Real.rpow_nonneg (forward_ratio_pos t ht.1.le zc).le _
        have hd:‖densityPair f h3 z‖=(reciprocalVolume z)^3*‖densityPair f h z‖:=by
          change ‖densityPair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))) z‖=_
          rw [inverse_cube_density,norm_mul,←Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hu 3)]
        rw [weightedKappaKernel_point a t ht.1 f h zc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hp.1 hr),hd]
        have hcoef:((heatKappa t z)^2/t)*(forwardRatio t z)^a≤18*(reciprocalVolume z)^3*(1+C):=
          (mul_le_mul hp.2 hc hr (by positivity)).trans_eq (by ring)
        calc
          _ ≤ (18*(reciprocalVolume z)^3*(1+C))*‖densityPair f h z‖ :=
            mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
          _ = 18*(1+C)*((reciprocalVolume z)^3*‖densityPair f h z‖) := by ring
      · rw [weightedKappaKernel_zero a t f h z hz,norm_zero]
        positivity)
  have hh:=tendsto_integral_filter_of_dominated_convergence
    (μ:=GaussHistoryHilbert.configurationMeasure) (F:=fun t z=>weightedKappaKernel a t f h z)
    (f:=fun z:SourceCoordinateSlice=>((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z)
    (fun z=>18*(1+C)*‖densityPair f h3 z‖)
    (Eventually.of_forall (fun t=>(weightedKappaKernel_integrable a t f h).aestronglyMeasurable)) hdom
    ((densityPair_integrable f h3).norm.const_mul (18*(1+C)))
    (Eventually.of_forall (fun z=>weightedKappaKernel_limit a f h z))
  have htarget:(∫z:SourceCoordinateSlice,((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z
      ∂GaussHistoryHilbert.configurationMeasure)=(18:ℂ)*sourcePair f h3:=by
    have he(z:SourceCoordinateSlice):((18*(reciprocalVolume z)^3:ℝ):ℂ)*densityPair f h z=
        (18:ℂ)*densityPair f h3 z:=by
      change _=(18:ℂ)*densityPair f (inverseVolumeAction (inverseVolumeAction (inverseVolumeAction h))) z
      rw [inverse_cube_density]
      push_cast
      ring
    simp_rw [he]
    rw [integral_const_mul,←sourcePair_integral]
  simpa only [weightedKappaKernel_integral,htarget,h3] using hh

private def sourceRowRate(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  ((forwardRatio t z)^(1/3:ℝ))⁻¹*forwardRatio t z/6
private theorem sourceRowRate_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (sourceRowRate t) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  have hp:0<(forwardRatio t z.val)^(1/3:ℝ):=Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _
  exact (((hr.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').inv hp.ne').mul hr).div_const 6
private theorem sourceRowRate_square(t:ℝ)(ht:0<t)(z:physicalChart):
    sourceRowRate t z.val^2=(forwardRatio t z.val)^(4/3:ℝ)/36:=by
  have hr:=forward_ratio_pos t ht.le z
  have hs:((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val=
      (forwardRatio t z.val)^(2/3:ℝ):=by
    rw [show (2/3:ℝ)=1-(1/3:ℝ) by norm_num,Real.rpow_sub hr]
    simp only [Real.rpow_one,div_eq_mul_inv,mul_comm]
  have hq:((forwardRatio t z.val)^(2/3:ℝ))^2=(forwardRatio t z.val)^(4/3:ℝ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    norm_num
  change (((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val/6)^2=_
  calc
    _=(((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val)^2/36:=by ring
    _=_:=by rw [hs,hq]
private theorem original_stochastic_radial(t:ℝ)(ht:0<t)(i:Fin 6):
    stochasticCoframeRow t ht i=radialColumn (sourceRowRate t) (sourceRowRate_smooth t ht) i*
      kappaAction t ht*combinedGenerator:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (GaussCoframeCore.momentum i f z word-(3*Complex.I*t:ℂ)*
      (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*1)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))-
    ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
    (GaussCoframeCore.momentum i f z word-(3*Complex.I*t:ℂ)*
      (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      (Complex.I*0)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word))=
    Complex.I*((sourceRowRate t z:ℂ)*((volumeGradient z i:ℂ)*
      ((heatKappa t z:ℂ)*combinedGenerator f z word)))
  unfold sourceRowRate
  push_cast
  ring
private theorem sourceRadialPrice_weight(t:ℝ)(ht:0<t):
    radialPrice (sourceRowRate t) (sourceRowRate_smooth t ht)=
      (sourceTime 0/48:ℂ) •
        (SourceCoframeVolume.volumeAction*gaussianProfileWeight t ht (4/3)):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (((3*sourceTime 0/4)*volume z*sourceRowRate t z^2:ℝ):ℂ) • f z=
      (sourceTime 0/48:ℂ) • ((volume z:ℂ) • ((((forwardRatio t z)^(4/3:ℝ):ℝ):ℂ) • f z))
    rw [sourceRowRate_square t ht ⟨z,hz⟩]
    push_cast
    module
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem pair_smul_right(a:ℂ)(f g:QuantumTest):sourcePair f (a • g)=a*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem volume_weight_kappa(t:ℝ)(ht:0<t)(g:QuantumTest):
    SourceCoframeVolume.volumeAction
      (gaussianProfileWeight t ht (4/3) (kappaAction t ht g))=
    gaussianProfileWeight t ht (4/3)
      (kappaAction t ht (SourceCoframeVolume.volumeAction g)):=by
  apply DFunLike.ext
  intro z
  change (volume z:ℂ) • ((((forwardRatio t z)^(4/3:ℝ):ℝ):ℂ) • ((heatKappa t z:ℂ) • g z))=
    (((forwardRatio t z)^(4/3:ℝ):ℝ):ℂ) • ((heatKappa t z:ℂ) • ((volume z:ℂ) • g z))
  simp only [smul_smul]
  ring
private theorem original_stochastic_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g)))=
    (sourceTime 0/48:ℂ)*sourcePair (combinedGenerator f)
      (kappaAction t ht (gaussianProfileWeight t ht (4/3)
        (kappaAction t ht (SourceCoframeVolume.volumeAction (combinedGenerator g))))):=by
  simp_rw [original_stochastic_radial]
  simp only [Module.End.mul_apply]
  rw [actual_radial_covariance_pair]
  change sourcePair (kappaAction t ht (combinedGenerator f))
    ((radialPrice (sourceRowRate t) (sourceRowRate_smooth t ht)) (kappaAction t ht (combinedGenerator g)))=_
  rw [sourceRadialPrice_weight]
  change sourcePair (kappaAction t ht (combinedGenerator f))
    ((sourceTime 0/48:ℂ) • SourceCoframeVolume.volumeAction
      (gaussianProfileWeight t ht (4/3) (kappaAction t ht (combinedGenerator g))))=_
  rw [pair_smul_right]
  rw [←volume_weight_kappa t ht (combinedGenerator g)]
  exact congrArg ((sourceTime 0/48:ℂ)*·)
    ((multiply_pair _ _ (combinedGenerator f)
      (SourceCoframeVolume.volumeAction
        (gaussianProfileWeight t ht (4/3) (kappaAction t ht (combinedGenerator g))))).symm)

theorem actual_stochastic_coframe_full36_first_jet(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
        (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((sourceTime 0/48:ℂ)*((18:ℂ)*sourcePair (combinedGenerator f)
        (inverseVolumeAction (inverseVolumeAction
          (inverseVolumeAction (SourceCoframeVolume.volumeAction (combinedGenerator g)))))))):=by
  have h:= (actual_heat_weighted_kappa_square_source_pair_first_jet (4/3)
    (combinedGenerator f) (SourceCoframeVolume.volumeAction (combinedGenerator g))).const_mul
      (sourceTime 0/48:ℂ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht':0<t:=ht
  simp only [dif_pos ht']
  rw [original_stochastic_pair t ht' f g]
  ring

private theorem volumeGradient_smooth(i:Fin 6):ContDiff ℝ ∞ (fun z:SourceCoordinateSlice=>volumeGradient z i):=by
  fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
def sourceCurrentColumn(i:Fin 6):QuantumTest→ₗ[ℂ]QuantumTest:=
  multiply (fun z=>reciprocalVolume z*volumeGradient z i)
    (fun z=>(reciprocal_volume_smooth z).mul (volumeGradient_smooth i).contDiffAt)
def coframeDriftColumn(i:Fin 6):QuantumTest→ₗ[ℂ]QuantumTest:=
  (-3*Complex.I:ℂ) • (sourceCurrentColumn i*SourceClockPhiNativeMatchedSource.matchedTester)
private theorem deterministic_row_source(t:ℝ)(ht:0<t)(i:Fin 6):
    deterministicCoframeRow t ht i=
      gaussianProfileWeight t ht (-1/3)*
        (SourceCoframeCovariantAction.covariantMomentum i+(t:ℂ) • coframeDriftColumn i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  swap
  · have hzero(q:QuantumTest):q z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
  apply PiLp.ext
  intro word
  simp only [deterministicCoframeRow,covariantHeatRow,
    ClockPhiHeatHamiltonianWork.heatCoframeRow,
    SourceCoframeCovariantAction.covariantMomentum,coframeDriftColumn,
    Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply]
  simp only [Complex.ofReal_zero,mul_zero,zero_smul,add_zero]
  change ((((forwardRatio t z)^(1/3:ℝ))⁻¹:ℝ):ℂ)*
      (GaussCoframeCore.momentum i f z word-(3*Complex.I*t:ℂ)*
        (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
          SourceClockPhiNativeMatchedSource.matchedTester f z word))+
      (((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ)*
        (SourceCoframeCovariantAction.connectionAction i f z word)=
      (((forwardRatio t z)^(-1/3:ℝ):ℝ):ℂ)*
        (GaussCoframeCore.momentum i f z word+
          SourceCoframeCovariantAction.connectionAction i f z word+
          (t:ℂ)*((-3*Complex.I:ℂ)*
            (((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
              SourceClockPhiNativeMatchedSource.matchedTester f z word)))
  have hr:((forwardRatio t z)^(1/3:ℝ))⁻¹=(forwardRatio t z)^(-1/3:ℝ):=
    by simpa only [neg_div] using (Real.rpow_neg (forward_ratio_pos t ht.le ⟨z,hz⟩).le (1/3:ℝ)).symm
  rw [hr]
  ring

private theorem profile_power_smooth(t:ℝ)(ht:0<t)(a:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(forwardRatio t x)^a) z.val:=by
  have h:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact h.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne'

private theorem weighted_metric_pair(t:ℝ)(ht:0<t)(a:ℝ)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (gaussianProfileWeight t ht a f)
      (SourceCoframeCovariantAction.metricAction i j (gaussianProfileWeight t ht a g))=
    sourcePair f (gaussianProfileWeight t ht (2*a)
      (SourceCoframeCovariantAction.metricAction i j g)):=by
  let M:=SourceCoframeCovariantAction.metricAction i j
  have hp:= (GaussNativeForm.multiply_pair
    (fun z=>(forwardRatio t z)^a)
    (profile_power_smooth t ht a)
    f (M (gaussianProfileWeight t ht a g))).symm
  change sourcePair (gaussianProfileWeight t ht a f)
    (M (gaussianProfileWeight t ht a g))=
    sourcePair f (gaussianProfileWeight t ht a (M (gaussianProfileWeight t ht a g))) at hp
  rw [hp]
  congr 1
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (((forwardRatio t z)^a:ℝ):ℂ) •
      ((GaussCoframeKinetic.coefficient i j z:ℂ) •
        ((((forwardRatio t z)^a:ℝ):ℂ) • g z))=
      (((forwardRatio t z)^(2*a):ℝ):ℂ) •
        ((GaussCoframeKinetic.coefficient i j z:ℂ) • g z)
    have hr:((forwardRatio t z)^a)^2=(forwardRatio t z)^(2*a):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (forward_ratio_pos t ht.le ⟨z,hz⟩).le]
      congr 1
      ring
    have he:(forwardRatio t z)^a*(GaussCoframeKinetic.coefficient i j z*(forwardRatio t z)^a)=
        (forwardRatio t z)^(2*a)*GaussCoframeKinetic.coefficient i j z:=by
      calc
        _=((forwardRatio t z)^a)^2*GaussCoframeKinetic.coefficient i j z:=by ring
        _=_:=by rw [hr]
    simp only [smul_smul,←Complex.ofReal_mul,he]
  · have hzero(q:QuantumTest):q z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm

private theorem deterministic_pair_weighted(t:ℝ)(ht:0<t)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (deterministicCoframeRow t ht i f)
      (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))=
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i f+
      (t:ℂ) • coframeDriftColumn i f)
      (gaussianProfileWeight t ht (-2/3)
        (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j g+
            (t:ℂ) • coframeDriftColumn j g))):=by
  rw [deterministic_row_source t ht i,deterministic_row_source t ht j]
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply]
  simpa only [show (2:ℝ)*(-1/3)=(-2/3:ℝ) by norm_num] using
    weighted_metric_pair t ht (-1/3) i j
      (SourceCoframeCovariantAction.covariantMomentum i f+(t:ℂ) • coframeDriftColumn i f)
      (SourceCoframeCovariantAction.covariantMomentum j g+(t:ℂ) • coframeDriftColumn j g)

private theorem weighted_pair_tendsto_zero(a:ℝ)(f h:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then sourcePair f (gaussianProfileWeight t ht a h) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (sourcePair f h)):=by
  have ht:Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)):=by
    simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hj:=actual_gaussian_weighted_source_pair_first_jet a f h
  have hh: Tendsto (fun t:ℝ=>sourcePair f h+(t:ℂ)*
      (if hp:0<t then (t:ℂ)⁻¹*
        (sourcePair f (gaussianProfileWeight t hp a h)-sourcePair f h) else 0))
      (𝓝[>] (0:ℝ)) (𝓝 (sourcePair f h)):=by
    simpa using tendsto_const_nhds.add (ht.mul hj)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  have hn:(t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hp.ne'
  simp only [dif_pos hp]
  field_simp [hn]
  ring

private theorem weighted_affine_pair_first_jet(a:ℝ)(f₀ f₁ h₀ h₁:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (sourcePair (f₀+(t:ℂ) • f₁)
        (gaussianProfileWeight t ht a (h₀+(t:ℂ) • h₁))-sourcePair f₀ h₀) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((18*a:ℂ)*sourcePair f₀ (inverseVolumeAction h₀)+
        sourcePair f₁ h₀+sourcePair f₀ h₁)):=by
  have ht:Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)):=by
    simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hj:=actual_gaussian_weighted_source_pair_first_jet a f₀ h₀
  have h10:=weighted_pair_tendsto_zero a f₁ h₀
  have h01:=weighted_pair_tendsto_zero a f₀ h₁
  have h11:=weighted_pair_tendsto_zero a f₁ h₁
  have hsum:=((hj.add h10).add h01).add (ht.mul h11)
  have hlim:Tendsto
      (fun t:ℝ=>(if hp:0<t then (t:ℂ)⁻¹*
        (sourcePair f₀ (gaussianProfileWeight t hp a h₀)-sourcePair f₀ h₀) else 0)+
        (if hp:0<t then sourcePair f₁ (gaussianProfileWeight t hp a h₀) else 0)+
        (if hp:0<t then sourcePair f₀ (gaussianProfileWeight t hp a h₁) else 0)+
        (t:ℂ)*(if hp:0<t then sourcePair f₁ (gaussianProfileWeight t hp a h₁) else 0))
      (𝓝[>] (0:ℝ))
      (𝓝 ((18*a:ℂ)*sourcePair f₀ (inverseVolumeAction h₀)+
        sourcePair f₁ h₀+sourcePair f₀ h₁)):=by
    convert hsum using 1
    ring
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  have hn:(t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hp.ne'
  simp only [dif_pos hp]
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  field_simp [hn]
  ring

private theorem deterministic_row_pair_first_jet(i j:Fin 6)(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (sourcePair (deterministicCoframeRow t ht i f)
        (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))-
       sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j g))) else 0)
      (𝓝[>] (0:ℝ))
      (𝓝 ((-12:ℂ)*sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        (inverseVolumeAction (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j g)))+
        sourcePair (coframeDriftColumn i f)
          (SourceCoframeCovariantAction.metricAction i j
            (SourceCoframeCovariantAction.covariantMomentum j g))+
        sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
          (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j g)))):=by
  have h:=weighted_affine_pair_first_jet (-2/3)
    (SourceCoframeCovariantAction.covariantMomentum i f) (coframeDriftColumn i f)
    (SourceCoframeCovariantAction.metricAction i j
      (SourceCoframeCovariantAction.covariantMomentum j g))
    (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j g))
  have hc:(18:ℂ)*((-2/3:ℝ):ℂ)=(-12:ℂ):=by norm_num
  rw [←hc]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  simp only [dif_pos hp,deterministic_pair_weighted,LinearMap.map_add,
    LinearMap.map_smul]

private def deterministicPairAt(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair (deterministicCoframeRow t ht i f)
    (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))
private def deterministicPairZero(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
    (SourceCoframeCovariantAction.metricAction i j
      (SourceCoframeCovariantAction.covariantMomentum j g))
def deterministicPairJet(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,(
    (-12:ℂ)*sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
      (inverseVolumeAction (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j g)))+
    sourcePair (coframeDriftColumn i f)
      (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j g))+
    sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
      (SourceCoframeCovariantAction.metricAction i j (coframeDriftColumn j g)))

theorem actual_deterministic_coframe_full36_first_jet(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (deterministicPairAt t ht f g-deterministicPairZero f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (deterministicPairJet f g)):=by
  have hsum:=tendsto_finsetSum (Finset.univ:Finset (Fin 6)) (fun i _=>
    tendsto_finsetSum (Finset.univ:Finset (Fin 6)) (fun j _=>
      deterministic_row_pair_first_jet i j f g))
  have hlim:Tendsto (fun t:ℝ=>∑i:Fin 6,∑j:Fin 6,
      (if ht:0<t then (t:ℂ)⁻¹*
        (sourcePair (deterministicCoframeRow t ht i f)
          (SourceCoframeCovariantAction.metricAction i j (deterministicCoframeRow t ht j g))-
         sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
          (SourceCoframeCovariantAction.metricAction i j
            (SourceCoframeCovariantAction.covariantMomentum j g))) else 0))
      (𝓝[>] (0:ℝ)) (𝓝 (deterministicPairJet f g)):=by
    simpa only [deterministicPairJet] using hsum
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  simp only [dif_pos hp,deterministicPairAt,deterministicPairZero]
  simp only [Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

private def localVolumeAction:QuantumTest→ₗ[ℂ]QuantumTest:=
  GaussNativeForm.multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private theorem local_coframe_gaussian(t:ℝ)(ht:0<t)(f g:QuantumTest):
    localCoframePair t ht f g=
      sourcePair f (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder g))+
      sourcePair f (gaussianProfileWeight t ht (-2/3) (GaussCoframeForm.numberShift g))+
      sourcePair f (gaussianProfileWeight t ht (4/3) (localVolumeAction g)):=by
  rfl
private def localPairZero(f g:QuantumTest):ℂ:=
  sourcePair f (SourceCoframeCovariantSquare.spinRemainder g)+
  sourcePair f (GaussCoframeForm.numberShift g)+
  sourcePair f (localVolumeAction g)
def localPairJet(f g:QuantumTest):ℂ:=
  (-12:ℂ)*sourcePair f (inverseVolumeAction (SourceCoframeCovariantSquare.spinRemainder g))+
  (-12:ℂ)*sourcePair f (inverseVolumeAction (GaussCoframeForm.numberShift g))+
  (24:ℂ)*sourcePair f (inverseVolumeAction (localVolumeAction g))

theorem actual_local_coframe_first_jet(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (localCoframePair t ht f g-localPairZero f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (localPairJet f g)):=by
  have h1:=actual_gaussian_weighted_source_pair_first_jet (-2/3) f
    (SourceCoframeCovariantSquare.spinRemainder g)
  have h2:=actual_gaussian_weighted_source_pair_first_jet (-2/3) f
    (GaussCoframeForm.numberShift g)
  have h3:=actual_gaussian_weighted_source_pair_first_jet (4/3) f
    (localVolumeAction g)
  have hsum:=(h1.add h2).add h3
  have hlim:Tendsto (fun t:ℝ=>
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f
        (gaussianProfileWeight t ht (-2/3) (SourceCoframeCovariantSquare.spinRemainder g))-
        sourcePair f (SourceCoframeCovariantSquare.spinRemainder g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f
        (gaussianProfileWeight t ht (-2/3) (GaussCoframeForm.numberShift g))-
        sourcePair f (GaussCoframeForm.numberShift g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f
        (gaussianProfileWeight t ht (4/3) (localVolumeAction g))-
        sourcePair f (localVolumeAction g)) else 0))
      (𝓝[>] (0:ℝ)) (𝓝 (localPairJet f g)):=by
    convert hsum using 1
    simp only [localPairJet]
    push_cast
    ring
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  simp only [dif_pos hp,local_coframe_gaussian,localPairZero]
  ring

private def nativePairAt(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))+
  sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))+
  sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g))-
  2*sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))+
  sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))+
  sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))+
  sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g))
private def nativePairZero(f g:QuantumTest):ℂ:=
  sourcePair f (scalarKinetic g)+sourcePair f (gaugeKinetic g)+
  sourcePair f (GaussMatterCore.matterAction g)+sourcePair f (centeredAction g)-
  2*sourcePair f (vacuumLinearAction g)+sourcePair f (vacuumConstantAction g)+
  sourcePair f (scalarSpatialAction g)+sourcePair f (magneticAction g)
def nativePairJet(f g:QuantumTest):ℂ:=
  (-14:ℂ)*sourcePair f (inverseVolumeAction (scalarKinetic g))+
  (22:ℂ)*sourcePair f (inverseVolumeAction (gaugeKinetic g))+
  (-2:ℂ)*sourcePair f (inverseVolumeAction (GaussMatterCore.matterAction g))+
  (34:ℂ)*sourcePair f (inverseVolumeAction (centeredAction g))-
  (56:ℂ)*sourcePair f (inverseVolumeAction (vacuumLinearAction g))+
  (24:ℂ)*sourcePair f (inverseVolumeAction (vacuumConstantAction g))+
  (12:ℂ)*sourcePair f (inverseVolumeAction (scalarSpatialAction g))+
  (16:ℂ)*sourcePair f (inverseVolumeAction (magneticAction g))

theorem actual_native_eight_first_jet(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (nativePairAt t ht f g-nativePairZero f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (nativePairJet f g)):=by
  have h1:=actual_gaussian_weighted_source_pair_first_jet (-7/9) f (scalarKinetic g)
  have h2:=actual_gaussian_weighted_source_pair_first_jet (11/9) f (gaugeKinetic g)
  have h3:=actual_gaussian_weighted_source_pair_first_jet (-1/9) f (GaussMatterCore.matterAction g)
  have h4:=actual_gaussian_weighted_source_pair_first_jet (17/9) f (centeredAction g)
  have h5:=actual_gaussian_weighted_source_pair_first_jet (14/9) f (vacuumLinearAction g)
  have h6:=actual_gaussian_weighted_source_pair_first_jet (12/9) f (vacuumConstantAction g)
  have h7:=actual_gaussian_weighted_source_pair_first_jet (6/9) f (scalarSpatialAction g)
  have h8:=actual_gaussian_weighted_source_pair_first_jet (8/9) f (magneticAction g)
  have hsum:=(((((((h1.add h2).add h3).add h4).sub (h5.const_mul 2)).add h6).add h7).add h8)
  have hlim:Tendsto (fun t:ℝ=>
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (-7/9) (scalarKinetic g))-sourcePair f (scalarKinetic g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (11/9) (gaugeKinetic g))-sourcePair f (gaugeKinetic g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (-1/9) (GaussMatterCore.matterAction g))-sourcePair f (GaussMatterCore.matterAction g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (17/9) (centeredAction g))-sourcePair f (centeredAction g)) else 0)-
      2*(if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (14/9) (vacuumLinearAction g))-sourcePair f (vacuumLinearAction g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (12/9) (vacuumConstantAction g))-sourcePair f (vacuumConstantAction g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (6/9) (scalarSpatialAction g))-sourcePair f (scalarSpatialAction g)) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(sourcePair f (gaussianProfileWeight t ht (8/9) (magneticAction g))-sourcePair f (magneticAction g)) else 0))
      (𝓝[>] (0:ℝ)) (𝓝 (nativePairJet f g)):=by
    convert hsum using 1
    simp only [nativePairJet]
    push_cast
    ring
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  simp only [dif_pos hp,nativePairAt,nativePairZero]
  ring

private def stochasticPairAt(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 6,∑j:Fin 6,sourcePair (stochasticCoframeRow t ht i f)
    (SourceCoframeCovariantAction.metricAction i j (stochasticCoframeRow t ht j g))
def stochasticPairJet(f g:QuantumTest):ℂ:=
  (sourceTime 0/48:ℂ)*((18:ℂ)*sourcePair (combinedGenerator f)
    (inverseVolumeAction (inverseVolumeAction
      (inverseVolumeAction (SourceCoframeVolume.volumeAction (combinedGenerator g))))))
private def wholePairZero(f g:QuantumTest):ℂ:=
  nativePairZero f g+deterministicPairZero f g+localPairZero f g
def wholePairJet(f g:QuantumTest):ℂ:=
  nativePairJet f g+deterministicPairJet f g+stochasticPairJet f g+localPairJet f g
private theorem whole_pair_decompose(t:ℝ)(ht:0<t)(f g:QuantumTest):
    wholeGaussianHeatHamiltonianPair t ht f g=
      nativePairAt t ht f g+deterministicPairAt t ht f g+
        stochasticPairAt t ht f g+localCoframePair t ht f g:=by
  unfold wholeGaussianHeatHamiltonianPair nativePairAt deterministicPairAt stochasticPairAt
  simp only [Finset.sum_add_distrib]
  ring

theorem actual_original_whole_gaussian_first_jet_source(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (wholeGaussianHeatHamiltonianPair t ht f g-wholePairZero f g) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (wholePairJet f g)):=by
  have h1:=actual_native_eight_first_jet f g
  have h2:=actual_deterministic_coframe_full36_first_jet f g
  have h3:=actual_stochastic_coframe_full36_first_jet f g
  have h4:=actual_local_coframe_first_jet f g
  have hsum:=((h1.add h2).add h3).add h4
  have hlim:Tendsto (fun t:ℝ=>
      (if ht:0<t then (t:ℂ)⁻¹*(nativePairAt t ht f g-nativePairZero f g) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(deterministicPairAt t ht f g-deterministicPairZero f g) else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*stochasticPairAt t ht f g else 0)+
      (if ht:0<t then (t:ℂ)⁻¹*(localCoframePair t ht f g-localPairZero f g) else 0))
      (𝓝[>] (0:ℝ)) (𝓝 (wholePairJet f g)):=by
    simpa only [wholePairJet,stochasticPairJet,stochasticPairAt] using hsum
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  have hp:0<t:=htpos
  simp only [dif_pos hp,whole_pair_decompose,wholePairZero]
  ring

private abbrev centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*‖scalarField z‖^2
private abbrev vacLinValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*inner ℝ vacuum (scalarField z)
private abbrev vacConstValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*volume z*‖vacuum‖^2
private abbrev spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*volume z/2*∑i:Fin 3,∑j:Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem potential_decompose(z:SourceCoordinateSlice):
    potential z=centerValue z-2*vacLinValue z+vacConstValue z+spatialValue z+magneticPotential z:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hn:=norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centerValue vacLinValue vacConstValue spatialValue
  rw [real_inner_self_eq_norm_sq,hn]
  ring
private theorem potential_action_decompose:
    multiply potential potential_smooth=centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (potential z:ℂ) • f z=(centerValue z:ℂ) • f z-
    (2:ℂ) • ((vacLinValue z:ℂ) • f z)+(vacConstValue z:ℂ) • f z+
      (spatialValue z:ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]
private theorem original_H0_split:
    GaussDiagonalHistory.diagonalAction=
      scalarKinetic+gaugeKinetic+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction+
      centeredAction-(2:ℂ) • vacuumLinearAction+vacuumConstantAction+
      scalarSpatialAction+magneticAction:=by
  unfold GaussDiagonalHistory.diagonalAction GaussNativeForm.nativeAction
  rw [potential_action_decompose]
  abel

private theorem coframe_zero_pair(f g:QuantumTest):
    sourcePair f (GaussCoframeForm.coframeAction g)=
      deterministicPairZero f g+localPairZero f g:=by
  rw [SourceCoframeCovariantSquare.original_coframe_covariant]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  have hk:sourcePair f (SourceCoframeCovariantAction.covariantKinetic g)=
      deterministicPairZero f g:=by
    simp only [SourceCoframeCovariantAction.covariantKinetic,LinearMap.sum_apply,
      sourcePair,map_sum,inner_sum,deterministicPairZero]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change sourcePair f (SourceCoframeCovariantAction.covariantAdjoint i
      (SourceCoframeCovariantAction.metricAction i j
        (SourceCoframeCovariantAction.covariantMomentum j g)))=
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        (SourceCoframeCovariantAction.metricAction i j
          (SourceCoframeCovariantAction.covariantMomentum j g))
    have had(p q:QuantumTest):sourcePair p (SourceCoframeCovariantAction.covariantAdjoint i q)=
        sourcePair (SourceCoframeCovariantAction.covariantMomentum i p) q:=by
      simp only [SourceCoframeCovariantAction.covariantAdjoint,
        SourceCoframeCovariantAction.covariantMomentum,LinearMap.add_apply,
        sourcePair,map_add,inner_add_left,inner_add_right]
      exact congrArg₂ (·+·) (GaussCoframeKinetic.adjoint_pair i p q)
        (SourceCoframeCovariantAction.original_connection_pair i p q)
    exact had f _
  change sourcePair f (SourceCoframeCovariantAction.covariantKinetic g)+
      sourcePair f (SourceCoframeCovariantSquare.spinRemainder g)+
      sourcePair f (GaussCoframeForm.numberShift g)+
      sourcePair f (localVolumeAction g)=_
  rw [hk]
  unfold localPairZero localVolumeAction
  ring

private theorem whole_pair_zero_H0(f g:QuantumTest):
    wholePairZero f g=sourcePair f (GaussDiagonalHistory.diagonalAction g):=by
  rw [original_H0_split]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
  change wholePairZero f g=sourcePair f (scalarKinetic g)+sourcePair f (gaugeKinetic g)+
    sourcePair f (GaussCoframeForm.coframeAction g)+sourcePair f (GaussMatterCore.matterAction g)+
    sourcePair f (centeredAction g)-2*sourcePair f (vacuumLinearAction g)+
    sourcePair f (vacuumConstantAction g)+sourcePair f (scalarSpatialAction g)+
    sourcePair f (magneticAction g)
  rw [coframe_zero_pair]
  unfold wholePairZero nativePairZero
  ring

theorem actual_original_whole_gaussian_first_jet_H0(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      (wholeGaussianHeatHamiltonianPair t ht f g-
        sourcePair f (GaussDiagonalHistory.diagonalAction g)) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 (wholePairJet f g)):=by
  simpa only [whole_pair_zero_H0] using actual_original_whole_gaussian_first_jet_source f g

end LowEnergy.SourceClockPhiOriginalGaussianH0FirstJet
