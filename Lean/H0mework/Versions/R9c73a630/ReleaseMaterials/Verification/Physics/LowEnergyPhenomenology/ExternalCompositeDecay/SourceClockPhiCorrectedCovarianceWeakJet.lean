import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCoframeWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedHamiltonianSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedCovarianceInfinitesimal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedCovarianceWeakJet
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCoframeWork ClockPhiCorrectedCovarianceInfinitesimal
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
private def gap(V t:ℝ):ℝ:=(1/V)^2-(1/(V+18*t))^2-
  2*((1/V-1/(V+18*t))/Real.sqrt (Real.log ((V+18*t)/V)))^2
private def covFactor(V t:ℝ):ℝ:=(3*sourceTime 0/8)*V*
  ((((V+18*t)/V)^(1/3:ℝ))⁻¹*((V+18*t)/V)/6)^2
private def covarianceValue(V t:ℝ):ℝ:=covFactor V t*gap V t
private def scalarControl(V t:ℝ):ℝ:=|covFactor V t| *(36/V^3)
private theorem value_point(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart):
    correctedCoframeCovariance t ht f z.val=(covarianceValue (volume z.val) t:ℂ) • f z.val:=by
  have h:=actual_corrected_covariance_point t ht f z
  have hlog:ClockPhiConservativeHeatSource.heatLog t z.val=Real.log ((volume z.val+18*t)/volume z.val):=by
    unfold ClockPhiConservativeHeatSource.heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  change correctedCoframeCovariance t ht f z.val=
    (((3*sourceTime 0/4)*volume z.val*(((forwardRatio t z.val)^(1/3:ℝ))⁻¹*forwardRatio t z.val/6)^2*
      ((1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2)-heatKappa t z.val^2):ℝ):ℂ) • f z.val at h
  rw [h]
  apply congrArg (fun r:ℝ=>(r:ℂ) • f z.val)
  unfold covarianceValue covFactor gap heatKappa SourceClockPhiForwardNativeReturn.forwardU forwardRatio
  rw [hlog]
  unfold reciprocalVolume
  simp only [one_div]
  ring
private theorem covFactor_continuous(V t:ℝ)(hV:0<V)(hW:0<V+18*t):
    ContinuousAt (fun p:ℝ×ℝ=>covFactor p.2 p.1) (t,V):=by
  have hv:ContinuousAt (fun p:ℝ×ℝ=>(p.2+18*p.1)/p.2) (t,V):=
    (continuousAt_snd.add (continuousAt_const.mul continuousAt_fst)).div continuousAt_snd hV.ne'
  have hr:0<(V+18*t)/V:=div_pos hW hV
  have hp:=hv.rpow_const (p:=(1/3:ℝ)) (Or.inl hr.ne')
  exact (continuousAt_const.mul continuousAt_snd).mul
    ((((hp.inv₀ (Real.rpow_pos_of_pos hr _).ne').mul hv).div_const 6).pow 2)
private theorem value_ratio_limit(V:ℝ)(hV:0<V):
    Tendsto (fun t:ℝ=>covarianceValue V t/t) (𝓝[>] 0) (𝓝 0):=by
  have hp:Tendsto (covFactor V) (𝓝[>] 0) (𝓝 (covFactor V 0)):=by
    have hm:ContinuousAt (fun t:ℝ=>(t,V)) 0:=continuousAt_id.prodMk continuousAt_const
    have h:ContinuousAt (covFactor V) 0:=(covFactor_continuous V 0 hV (by simpa using hV)).comp_of_eq hm rfl
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hg:=actual_clock_covariance_first_order_zero V hV
  have hh:=hp.mul hg
  simpa only [mul_zero,covarianceValue,gap,mul_div_assoc] using hh
private theorem value_ratio_bound(V t:ℝ)(hV:0<V)(ht:0<t):
    |covarianceValue V t/t| ≤ scalarControl V t:=by
  have h:=actual_clock_covariance_first_order_bound V t hV ht
  change 0 ≤ gap V t/t ∧ gap V t/t ≤ 36/V^3 at h
  unfold covarianceValue scalarControl
  rw [mul_div_assoc,abs_mul,abs_of_nonneg h.1]
  exact mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
private theorem field_control_continuous(p:ℝ×SourceCoordinateSlice)(ht:0 ≤ p.1)(hz:p.2∈physicalChart):
    ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>scalarControl (volume x.2) x.1) p:=by
  have hv:=volume_pos ⟨p.2,hz⟩
  have hW:0<volume p.2+18*p.1:=by positivity
  have hvol:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>volume x.2) p:=
    volume_smooth.continuous.continuousAt.comp continuousAt_snd
  have hm:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>(x.1,volume x.2)) p:=continuousAt_fst.prodMk hvol
  have hp:ContinuousAt (fun x:ℝ×SourceCoordinateSlice=>covFactor (volume x.2) x.1) p:=
    (covFactor_continuous _ _ hv hW).comp_of_eq hm rfl
  exact hp.abs.mul (continuousAt_const.div (hvol.pow 3) (pow_ne_zero 3 hv.ne'))
private theorem core_control(f:QuantumTest):∃C:ℝ,0 ≤ C ∧ ∀t∈Icc (0:ℝ) 1,∀z∈tsupport f,
    scalarControl (volume z) t ≤ C:=by
  have hc:ContinuousOn (fun x:ℝ×SourceCoordinateSlice=>scalarControl (volume x.2) x.1)
      (Icc (0:ℝ) 1×ˢtsupport f):=by
    intro p hp
    exact (field_control_continuous p hp.1.1 (f.tsupport_subset hp.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod f.hasCompactSupport).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht z hz
  exact (le_abs_self _).trans ((hC (t,z) ⟨ht,hz⟩).trans (le_max_left _ _))
private def kernel(t:ℝ)(f g:QuantumTest)(z:SourceCoordinateSlice):ℂ:=
  if ht:0<t then (t:ℂ)⁻¹*densityPair f (correctedCoframeCovariance t ht g) z else 0
private theorem kernel_point(t:ℝ)(ht:0<t)(f g:QuantumTest)(z:physicalChart):
    kernel t f g z.val=((covarianceValue (volume z.val) t/t:ℝ):ℂ)*densityPair f g z.val:=by
  unfold kernel
  rw [dif_pos ht]
  change (t:ℂ)⁻¹*inner ℂ (GaussFockWeights.weight (fun N=>GaussDensityCore.complexDensity N z.val) (f z.val))
    (correctedCoframeCovariance t ht g z.val)=_
  rw [value_point,inner_smul_right]
  change (t:ℂ)⁻¹*((covarianceValue (volume z.val) t:ℂ)*densityPair f g z.val)=_
  push_cast
  ring
private theorem kernel_zero(t:ℝ)(f g:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉tsupport f):
    kernel t f g z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport hz
  unfold kernel
  split_ifs <;> simp [densityPair,hf]
private theorem kernel_integrable(t:ℝ)(f g:QuantumTest):
    Integrable (kernel t f g) GaussHistoryHilbert.configurationMeasure:=by
  by_cases ht:0<t
  · apply ((densityPair_integrable f (correctedCoframeCovariance t ht g)).const_mul (t:ℂ)⁻¹).congr
    exact Eventually.of_forall (fun z=>by simp only [kernel,dif_pos ht])
  · apply (integrable_zero SourceCoordinateSlice ℂ GaussHistoryHilbert.configurationMeasure).congr
    exact Eventually.of_forall (fun z=>by simp only [Pi.zero_apply,kernel,dif_neg ht])
private theorem kernel_limit(f g:QuantumTest)(z:SourceCoordinateSlice):
    Tendsto (fun t:ℝ=>kernel t f g z) (𝓝[>] 0) (𝓝 0):=by
  by_cases hz:z∈physicalChart
  · have hr:=value_ratio_limit (volume z) (volume_pos ⟨z,hz⟩)
    have hh:=((Complex.continuous_ofReal.continuousAt.tendsto).comp hr).mul_const (densityPair f g z)
    simp only [Complex.ofReal_zero,zero_mul] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (kernel_point t ht f g ⟨z,hz⟩).symm
  · have hs:z∉tsupport f:=fun h=>hz (f.tsupport_subset h)
    simp only [kernel_zero _ f g z hs]
    exact tendsto_const_nhds
private theorem kernel_integral(t:ℝ)(f g:QuantumTest):
    (∫z,kernel t f g z ∂GaussHistoryHilbert.configurationMeasure)=
      if ht:0<t then (t:ℂ)⁻¹*sourcePair f (correctedCoframeCovariance t ht g) else 0:=by
  by_cases ht:0<t
  · simp only [kernel,dif_pos ht]
    rw [integral_const_mul,←sourcePair_integral]
  · simp only [kernel,dif_neg ht,integral_zero]

theorem actual_corrected_covariance_weak_first_order_zero(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*sourcePair f (correctedCoframeCovariance t ht g) else 0)
      (𝓝[>] 0) (𝓝 0):=by
  obtain ⟨C,hC,hbound⟩:=core_control f
  have hdom:∀ᶠ t : ℝ in 𝓝[>] 0,∀ᵐ z ∂GaussHistoryHilbert.configurationMeasure,
      ‖kernel t f g z‖ ≤ C*‖densityPair f g z‖:=by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num:(0:ℝ)<1)] with t ht
    exact Eventually.of_forall (fun z=>by
      by_cases hz:z∈tsupport f
      · rw [kernel_point t ht.1 f g ⟨z,f.tsupport_subset hz⟩,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          ((value_ratio_bound _ t (volume_pos ⟨z,f.tsupport_subset hz⟩) ht.1).trans
            (hbound t ⟨ht.1.le,ht.2.le⟩ z hz)) (norm_nonneg _)
      · rw [kernel_zero t f g z hz,norm_zero]
        positivity)
  have hh:=tendsto_integral_filter_of_dominated_convergence
    (μ:=GaussHistoryHilbert.configurationMeasure) (F:=fun t z=>kernel t f g z)
    (f:=fun _:SourceCoordinateSlice=>(0:ℂ)) (fun z=>C*‖densityPair f g z‖)
    (Eventually.of_forall (fun t=>(kernel_integrable t f g).aestronglyMeasurable)) hdom
    ((densityPair_integrable f g).norm.const_mul C)
    (Eventually.of_forall (fun z=>kernel_limit f g z))
  simpa only [kernel_integral,integral_zero] using hh


theorem actual_corrected_hamiltonian_first_order_agreement(f g:QuantumTest):
    Tendsto (fun t:ℝ=>if ht:0<t then (t:ℂ)⁻¹*
      ((∫x:ℝ×ℝ,sourcePair (ClockPhiHeatCorrectedCovarianceSource.correctedCompleteCore t ht x.1 x.2 f)
        (GaussDiagonalHistory.diagonalAction (ClockPhiHeatCorrectedCovarianceSource.correctedCompleteCore t ht x.1 x.2 g))
          ∂(ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1))-
        SourceClockPhiCompleteHeatHamiltonianSource.wholeGaussianHeatHamiltonianPair t ht f g) else 0)
      (𝓝[>] 0) (𝓝 0):=by
  have h:=actual_corrected_covariance_weak_first_order_zero
    (SourceClockPhiCombinedScalePressure.combinedGenerator f)
    (SourceClockPhiCombinedScalePressure.combinedGenerator g)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [(ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian t ht f g).2,
    add_sub_cancel_left]

end LowEnergy.ClockPhiCorrectedCovarianceWeakJet
