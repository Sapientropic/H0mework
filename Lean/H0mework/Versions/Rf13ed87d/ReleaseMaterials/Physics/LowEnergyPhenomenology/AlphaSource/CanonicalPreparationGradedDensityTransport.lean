import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldFullVertex
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCore
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGradedTransport
open GaussHistoryHilbert GaussDensityCore GaussCoreDifferential GaussFockPair GaussCoreHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets
open CanonicalPreparationCore
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators ENNReal

def densityCurve (f : Field289) (N : ℕ) (z : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  complexDensity N (fieldCoordinateCurve f r z)

def halfRatio (f : Field289) (N : ℕ) (z : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  coreHalfDensity N z / coreHalfDensity N (fieldCoordinateCurve f r z)

theorem curve_zero (f : Field289) (z : SourceCoordinateSlice) : fieldCoordinateCurve f 0 z=z := by
  simp only [fieldCoordinateCurve,zero_smul,add_zero]

theorem curve_valid_near (f : Field289) (z : physicalChart) :
    ∀ᶠr in 𝓝 (0:ℝ),fieldCoordinateCurve f r z.val∈physicalChart := by
  have c : Continuous (fun r : ℝ=>fieldCoordinateCurve f r z.val) := by
    unfold fieldCoordinateCurve; fun_prop
  exact c.continuousAt.preimage_mem_nhds (by simpa only [curve_zero] using physicalChart.isOpen.mem_nhds z.property)

theorem densityCurve_smooth (f : Field289) (N : ℕ) (z : SourceCoordinateSlice) (r : ℝ)
    (hr : fieldCoordinateCurve f r z∈physicalChart) : ContDiffAt ℝ ∞ (densityCurve f N z) r := by
  exact (complexDensity_smooth N ⟨_,hr⟩).comp r (by unfold fieldCoordinateCurve; fun_prop)

theorem halfRatio_smooth (f : Field289) (N : ℕ) (z : SourceCoordinateSlice) (r : ℝ)
    (hr : fieldCoordinateCurve f r z∈physicalChart) : ContDiffAt ℝ ∞ (halfRatio f N z) r := by
  unfold halfRatio
  have curve : ContDiffAt ℝ ∞ (fun t : ℝ=>fieldCoordinateCurve f t z) r := by
    unfold fieldCoordinateCurve; fun_prop
  have h := (coreHalfDensity_smooth N ⟨_,hr⟩).comp r curve
  have constant : ContDiffAt ℝ ∞ (fun _ : ℝ=>coreHalfDensity N z) r := contDiffAt_const
  convert! constant.mul (h.inv (coreHalfDensity_ne_zero N ⟨_,hr⟩)) using 1

def smoothCurveJets (F : ℝ → ℂ) (smooth : ∀ᶠr in 𝓝 (0:ℝ),ContDiffAt ℝ ∞ F r) : TwoJets F where
  first:=deriv F
  second:=deriv (deriv F) 0
  derivative_near:=smooth.mono fun r hr=>(hr.differentiableAt (by simp)).hasDerivAt
  second_derivative:=((smooth.self_of_nhds.derivWithin (m:=∞) (by simp)).differentiableAt (by simp)).hasDerivAt

def densityJets (f : Field289) (N : ℕ) (z : physicalChart) : TwoJets (densityCurve f N z.val) :=
  smoothCurveJets _ ((curve_valid_near f z).mono (fun r hr=>densityCurve_smooth f N z.val r hr))

def transportJets (f : Field289) (N : ℕ) (z : physicalChart) : TwoJets (halfRatio f N z.val) :=
  smoothCurveJets _ ((curve_valid_near f z).mono (fun r hr=>halfRatio_smooth f N z.val r hr))

theorem halfRatio_zero (f : Field289) (N : ℕ) (z : physicalChart) : halfRatio f N z.val 0=1 := by
  rw [halfRatio,curve_zero,div_self (coreHalfDensity_ne_zero N z)]

theorem half_square (N : ℕ) (z : physicalChart) : coreHalfDensity N z.val^2=complexDensity N z.val := by
  unfold coreHalfDensity complexDensity
  exact_mod_cast Real.sq_sqrt (density_pos N z).le

theorem halfRatio_density (f : Field289) (N : ℕ) (z : physicalChart) (r : ℝ)
    (hr : fieldCoordinateCurve f r z.val∈physicalChart) :
    halfRatio f N z.val r^2*densityCurve f N z.val r=complexDensity N z.val := by
  rw [halfRatio,div_pow,half_square N z,half_square N ⟨_,hr⟩]
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (density_pos N ⟨_,hr⟩).ne')

def transportFiber (f : Field289) (z : SourceCoordinateSlice) (r : ℝ) : FockFiber →L[ℂ] FockFiber :=
  GaussFockWeights.weight (fun N=>halfRatio f N z r)

theorem halfRatio_star (f : Field289) (N : ℕ) (z : SourceCoordinateSlice) (r : ℝ) :
    star (halfRatio f N z r)=halfRatio f N z r := by
  simp [halfRatio,coreHalfDensity,star_div]

theorem pair_transport (f : Field289) (z : physicalChart) (r : ℝ)
    (hr : fieldCoordinateCurve f r z.val∈physicalChart) (a b : FockFiber) :
    pairSample (fieldCoordinateCurve f r z.val) (transportFiber f z.val r a) (transportFiber f z.val r b)=
      pairSample z.val a b := by
  simp only [pairSample,transportFiber,GaussFockWeights.weight_apply,star_mul,halfRatio_star]
  apply Finset.sum_congr rfl
  intro word _
  calc
    _=(halfRatio f word.card z.val r^2*densityCurve f word.card z.val r)*star (a word)*b word:=by
      unfold densityCurve; ring
    _=complexDensity word.card z.val*star (a word)*b word:=by rw [halfRatio_density f word.card z r hr]

-- The weight is the original Number-dependent Hilbert measure, at every sector.
theorem densityCurve_original_measure (f : Field289) (N : ℕ) (z : physicalChart) :
    densityCurve f N z.val 0=(numberWeight N z:ℂ) := by rw [densityCurve,curve_zero]; rfl

theorem pair_transport_near (f : Field289) (z : physicalChart) (a b : FockFiber) :
    (fun r=>pairSample (fieldCoordinateCurve f r z.val) (transportFiber f z.val r a) (transportFiber f z.val r b))
      =ᶠ[𝓝 0] fun _=>pairSample z.val a b :=
  (curve_valid_near f z).mono (fun r hr=>pair_transport f z r hr a b)

def productJets {F G : ℝ → ℂ} (jf : TwoJets F) (jg : TwoJets G) : TwoJets (fun r=>F r*G r) where
  first r:=jf.first r*G r+F r*jg.first r
  second:=(jf.second*G 0+jf.first 0*jg.first 0)+(jf.first 0*jg.first 0+F 0*jg.second)
  derivative_near:=by
    filter_upwards [jf.derivative_near,jg.derivative_near] with r hf hg
    exact hf.mul hg
  second_derivative:=(jf.second_derivative.mul jg.actual.1).add (jf.actual.1.mul jg.second_derivative)

theorem transport_first_equation (f : Field289) (N : ℕ) (z : physicalChart) :
    2*(transportJets f N z).first 0*complexDensity N z.val+(densityJets f N z).first 0=0 := by
  let J:=productJets (productJets (transportJets f N z) (transportJets f N z)) (densityJets f N z)
  have same : (fun r=>(halfRatio f N z.val r*halfRatio f N z.val r)*densityCurve f N z.val r)=ᶠ[𝓝 0]
      fun _=>complexDensity N z.val := by
    filter_upwards [curve_valid_near f z] with r hr
    simpa only [pow_two] using halfRatio_density f N z r hr
  have h:=(J.actual.1.congr_of_eventuallyEq same.symm).unique (hasDerivAt_const 0 (complexDensity N z.val))
  change ((transportJets f N z).first 0*halfRatio f N z.val 0+halfRatio f N z.val 0*(transportJets f N z).first 0)*
    densityCurve f N z.val 0+halfRatio f N z.val 0*halfRatio f N z.val 0*(densityJets f N z).first 0=0 at h
  simp only [halfRatio_zero,densityCurve,curve_zero,mul_one,one_mul] at h
  linear_combination h

theorem transport_second_equation (f : Field289) (N : ℕ) (z : physicalChart) :
    2*(transportJets f N z).second*complexDensity N z.val+
      2*((transportJets f N z).first 0)^2*complexDensity N z.val+
      4*(transportJets f N z).first 0*(densityJets f N z).first 0+(densityJets f N z).second=0 := by
  let J:=productJets (productJets (transportJets f N z) (transportJets f N z)) (densityJets f N z)
  have same : (fun r=>(halfRatio f N z.val r*halfRatio f N z.val r)*densityCurve f N z.val r)=ᶠ[𝓝 0]
      fun _=>complexDensity N z.val := by
    filter_upwards [curve_valid_near f z] with r hr
    simpa only [pow_two] using halfRatio_density f N z r hr
  have h:=(J.actual.2.congr_of_eventuallyEq same.deriv.symm).unique (by simpa using hasDerivAt_const (0:ℝ) (0:ℂ))
  dsimp only [J,productJets] at h
  simp only [halfRatio_zero,densityCurve,curve_zero,mul_one,one_mul] at h
  linear_combination h

theorem transport_first (f : Field289) (N : ℕ) (z : physicalChart) :
    (transportJets f N z).first 0= -(densityJets f N z).first 0/(2*complexDensity N z.val) := by
  have nz : complexDensity N z.val≠0:=Complex.ofReal_ne_zero.mpr (density_pos N z).ne'
  apply (eq_div_iff (mul_ne_zero (by norm_num) nz)).mpr
  linear_combination transport_first_equation f N z

theorem scalar_second_transport (d v w u : ℂ) (hd : d≠0)
    (h : 2*u*d+2*(-v/(2*d))^2*d+4*(-v/(2*d))*v+w=0) :
    u=3*v^2/(4*d^2)-w/(2*d) := by
  field_simp at h ⊢
  ring_nf at h ⊢
  linear_combination 2*h

theorem transport_second (f : Field289) (N : ℕ) (z : physicalChart) :
    (transportJets f N z).second=
      3*((densityJets f N z).first 0)^2/(4*(complexDensity N z.val)^2)-
      (densityJets f N z).second/(2*complexDensity N z.val) := by
  apply scalar_second_transport _ _ _ _ (Complex.ofReal_ne_zero.mpr (density_pos N z).ne')
  simpa only [transport_first,complexDensity] using transport_second_equation f N z

def transportedPair (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ :=
  ∫z,pairSample (fieldCoordinateCurve f r z) (transportFiber f z r (a z)) (transportFiber f z r (b z)) ∂GaussHistoryHilbert.configurationMeasure

theorem transportedPair_original (f : Field289) (a b : QuantumTest) :
    transportedPair f a b=ᶠ[𝓝 0] fun _=>sourcePair a b := by
  have near : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f a :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [near] with r hr
  rw [transportedPair,sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    change pairSample (fieldCoordinateCurve f r z) (transportFiber f z r (a z)) (transportFiber f z r (b z))=densityPair a b z
    by_cases inside : z∈tsupport a
    · exact (pair_transport f ⟨z,a.tsupport_subset inside⟩ r (fieldRadius_chart f a r z hr.le inside) (a z) (b z)).trans
        (pairSample_source a b z)
    · have az : a z=0:=image_eq_zero_of_notMem_tsupport inside
      rw [az,map_zero]
      simp only [pairSample,WithLp.ofLp_zero,Pi.zero_apply,star_zero,mul_zero,zero_mul,Finset.sum_const_zero]
      rw [←pairSample_source a b z,az]
      simp only [pairSample,WithLp.ofLp_zero,Pi.zero_apply,star_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem transportedPair_jets (f : Field289) (a b : QuantumTest) :
    HasDerivAt (transportedPair f a b) 0 0 ∧ HasDerivAt (deriv (transportedPair f a b)) 0 0 := by
  constructor
  · exact (hasDerivAt_const (0:ℝ) (sourcePair a b)).congr_of_eventuallyEq (transportedPair_original f a b)
  · apply (hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq
    simpa using (transportedPair_original f a b).deriv

theorem density_continuous (N : ℕ) : Continuous (density N) := by
  have gauge : Continuous (fun z : SourceCoordinateSlice=>(z.2.2 : SourceQuantumConfigurationHilbert.Gauge)) := by fun_prop
  have volume : Continuous (fun z : SourceCoordinateSlice=>z.1 0*z.1 2*z.1 5) := by fun_prop
  exact (jacobian_continuous.comp gauge).mul (volume.pow _)

theorem chartCurve_continuous (f : Field289) (r : ℝ) :
    Continuous (fun z : physicalChart=>fieldCoordinateCurve f r z.val) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h : ContinuousAt (fun w : SourceCoordinateSlice=>fieldCoordinateCurve f r w) z.val :=
    (field_curve_smooth f r z).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
  exact h.comp continuous_subtype_val.continuousAt

def variedNumberMeasure (f : Field289) (N : ℕ) (r : ℝ) : Measure physicalChart :=
  chartMeasure.withDensity (fun z=>ENNReal.ofReal (density N (fieldCoordinateCurve f r z.val)))

theorem variedNumberMeasure_zero (f : Field289) (N : ℕ) : variedNumberMeasure f N 0=GaussHistoryHilbert.numberMeasure N := by
  simp only [variedNumberMeasure,curve_zero,GaussHistoryHilbert.numberMeasure,density_on_chart]

theorem transport_norm_density (f : Field289) (N : ℕ) (z : physicalChart) (r : ℝ)
    (hr : fieldCoordinateCurve f r z.val∈physicalChart) :
    ‖halfRatio f N z.val r‖^2*density N (fieldCoordinateCurve f r z.val)=density N z.val := by
  have h:=congrArg norm (halfRatio_density f N z r hr)
  simpa only [norm_mul,norm_pow,densityCurve,complexDensity,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (density_pos N z),abs_of_pos (density_pos N ⟨_,hr⟩)] using h

theorem transport_enorm_density (f : Field289) (N : ℕ) (z : physicalChart) (r : ℝ)
    (hr : fieldCoordinateCurve f r z.val∈physicalChart) :
    ENNReal.ofReal (density N (fieldCoordinateCurve f r z.val))*‖halfRatio f N z.val r‖ₑ^(2:ℝ)=
      ENNReal.ofReal (density N z.val) := by
  rw [ENNReal.rpow_two,←ofReal_norm,←ENNReal.ofReal_pow (norm_nonneg _) 2,
    ←ENNReal.ofReal_mul (density_pos N ⟨_,hr⟩).le]
  congr 1
  exact (mul_comm _ _).trans (transport_norm_density f N z r hr)

theorem eLpNorm_transport (f : Field289) (N : ℕ) (a : QuantumTest) (word : Occupation) (r : ℝ)
    (small : |r|≤fieldRadius f a) :
    eLpNorm (fun z : physicalChart=>halfRatio f N z.val r*a z.val word) 2 (variedNumberMeasure f N r)=
      eLpNorm (fun z : physicalChart=>a z.val word) 2 (GaussHistoryHilbert.numberMeasure N) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  have measurable : Measurable (fun z : physicalChart=>ENNReal.ofReal (density N (fieldCoordinateCurve f r z.val))) := by
    convert! (((density_continuous N).comp (chartCurve_continuous f r)).measurable.ennreal_ofReal) using 1
  rw [variedNumberMeasure,GaussHistoryHilbert.numberMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable
      (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (GaussHalfDensity.weight_measurable N) (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
  congr 1
  apply lintegral_congr_ae
  exact Eventually.of_forall fun z=>by
    simp only [Pi.mul_apply]
    by_cases inside : z.val∈tsupport a
    · simp only [enorm_mul,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤2),←mul_assoc]
      rw [transport_enorm_density f N z r (fieldRadius_chart f a r z.val small inside)]
      rfl
    · have az : a z.val=0:=image_eq_zero_of_notMem_tsupport inside
      simp only [az,WithLp.ofLp_zero,Pi.zero_apply,mul_zero,enorm_zero,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2),mul_zero]

theorem halfRatio_measurable (f : Field289) (N : ℕ) (r : ℝ) :
    Measurable (fun z : physicalChart=>halfRatio f N z.val r) := by
  have half : Continuous (coreHalfDensity N) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (density_continuous N))
  exact (half.comp continuous_subtype_val).measurable.div (half.comp (chartCurve_continuous f r)).measurable

theorem transportedSector_memLp (f : Field289) (N : ℕ) (a : QuantumTest) (word : Occupation) (r : ℝ)
    (small : |r|≤fieldRadius f a) :
    MemLp (fun z : physicalChart=>halfRatio f N z.val r*a z.val word) 2 (variedNumberMeasure f N r) := by
  constructor
  · exact (halfRatio_measurable f N r).aestronglyMeasurable.mul
      ((component word a).continuous.comp continuous_subtype_val).aestronglyMeasurable
  · rw [eLpNorm_transport f N a word r small]
    exact (scalarMemLp N (component word a)).2

def transportedSector (f : Field289) (N : ℕ) (a : QuantumTest) (word : Occupation) (r : ℝ)
    (small : |r|≤fieldRadius f a) : Lp ℂ 2 (variedNumberMeasure f N r) :=
  (transportedSector_memLp f N a word r small).toLp (fun z=>halfRatio f N z.val r*a z.val word)

theorem transportedSector_norm (f : Field289) (N : ℕ) (a : QuantumTest) (word : Occupation) (r : ℝ)
    (small : |r|≤fieldRadius f a) :
    ‖transportedSector f N a word r small‖=‖scalarLp N (component word a)‖ := by
  simp only [Lp.norm_def,transportedSector]
  rw [eLpNorm_congr_ae (transportedSector_memLp f N a word r small).coeFn_toLp,
    eLpNorm_congr_ae (scalarLp_ae N (component word a)),eLpNorm_transport f N a word r small]
  rfl

end LowEnergy.PreparationVacuumGradedTransport
