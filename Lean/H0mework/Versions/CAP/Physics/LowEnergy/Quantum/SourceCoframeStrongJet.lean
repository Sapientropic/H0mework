import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCoframeScaleTransport
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceCoframeStrongJet
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent SourceCoframeScaleTransport
open MeasureTheory Filter Set Function
open scoped ContDiff Topology InnerProductSpace ENNReal

private theorem outside_zero (f : QuantumTest) {z : SourceCoordinateSlice}
    (hz : z∉physicalChart) : f z=0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))

theorem dilation_flow (t : ℝ) (f : QuantumTest) :
    dilation (coreFlow t f)=coreFlow t (dilation f) := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · apply PiLp.ext
    intro word
    have hchart : scale (rate t) z∈physicalChart :=
      (scale_chart_iff _ (Real.exp_pos _) z).mpr hz
    have h₁ := coreFlow_generator (coreFlow t f) ⟨z,hz⟩ word
    have h₂ := (coreFlow_generator f ⟨scale (rate t) z,hchart⟩ word).const_mul
      ((Real.exp ((word.card+4 : ℝ)*t) : ℂ))
    have he : (fun s : ℝ => coreFlow s (coreFlow t f) z word)=
        (fun s => (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*
          coreFlow s f (scale (rate t) z) word) := by
      funext s
      rw [coreFlow_add,add_comm s t,←coreFlow_add t s f,coreFlow_apply]
    rw [he] at h₁
    have hd := h₁.unique h₂
    change Complex.I*dilation (coreFlow t f) z word=
      (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*(Complex.I*dilation f (scale (rate t) z) word) at hd
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [coreFlow_apply]
    linear_combination hd
  · rw [outside_zero _ hz,outside_zero _ hz]

theorem component_flow_derivative (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coreFlow s f z word)
      (Complex.I*coreFlow t (dilation f) z word) t := by
  by_cases hz : z∈physicalChart
  · have h := (coreFlow_generator (coreFlow t f) ⟨z,hz⟩ word).scomp_of_eq t
      ((hasDerivAt_id t).sub_const t) (by simp)
    have he : (fun s : ℝ => coreFlow (s-t) (coreFlow t f) z word)=
        (fun s => coreFlow s f z word) := by
      funext s
      rw [coreFlow_add,sub_add_cancel]
    simp only [one_smul,Function.comp_def,id_eq] at h
    rw [he,dilation_flow] at h
    exact h
  · have he : (fun s : ℝ => coreFlow s f z word)=fun _ => 0 := by
      funext s
      rw [outside_zero _ hz]
      rfl
    rw [he,outside_zero (coreFlow t (dilation f)) hz]
    simpa using hasDerivAt_const t (0 : ℂ)

theorem component_flow_continuous (f : QuantumTest) (word : Occupation) :
    Continuous (fun p : ℝ×SourceCoordinateSlice => coreFlow p.1 f p.2 word) := by
  change Continuous (fun p : ℝ×SourceCoordinateSlice =>
    (Real.exp ((word.card+4 : ℝ)*p.1) : ℂ)*f (scale (rate p.1) p.2) word)
  have hf : Continuous (fun z : SourceCoordinateSlice => f z word) := (component word f).continuous
  have hs : Continuous (fun p : ℝ×SourceCoordinateSlice => scale (rate p.1) p.2) := by
    unfold scale rate
    fun_prop
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (hf.comp hs)

private theorem density_continuous (N : ℕ) : Continuous (GaussDensityCore.complexDensity N) := by
  have hg : Continuous (fun z : SourceCoordinateSlice => (z.2.2 : Gauge)) := by fun_prop
  have hv : Continuous (fun z : SourceCoordinateSlice => z.1 0*z.1 2*z.1 5) := by fun_prop
  exact Complex.continuous_ofReal.comp
    ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))

private def kernel (f g : QuantumTest) (t : ℝ) (z : SourceCoordinateSlice) : ℂ :=
  densityPair f (coreFlow t g) z

private theorem kernel_continuous (f g : QuantumTest) :
    Continuous (fun p : ℝ×SourceCoordinateSlice => kernel f g p.1 p.2) := by
  have he : (fun p : ℝ×SourceCoordinateSlice => kernel f g p.1 p.2)=
      fun p => ∑ word : Occupation, GaussDensityCore.complexDensity word.card p.2*
        star (f p.2 word)*coreFlow p.1 g p.2 word := by
    funext p
    exact densityPair_sum _ _ _
  rw [he]
  apply continuous_finsetSum
  intro word _
  exact (((density_continuous word.card).comp continuous_snd).mul
    (((component word f).continuous.comp continuous_snd).star)).mul (component_flow_continuous g word)

private theorem kernel_derivative (f g : QuantumTest) (z : SourceCoordinateSlice) (t : ℝ) :
    HasDerivAt (fun s => kernel f g s z) (Complex.I*kernel f (dilation g) t z) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset Occupation)) (fun word _ =>
    (component_flow_derivative g z word t).const_mul
      (GaussDensityCore.complexDensity word.card z*star (f z word)))
  have he : (fun s => kernel f g s z)=fun s => ∑ word : Occupation,
      GaussDensityCore.complexDensity word.card z*star (f z word)*coreFlow s g z word := by
    funext s
    exact densityPair_sum _ _ _
  rw [he]
  convert! h using 1
  · funext s
    simp only [Finset.sum_apply]
  · unfold kernel
    rw [densityPair_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring

private theorem kernel_zero (f g : QuantumTest) (t : ℝ) (z : SourceCoordinateSlice)
    (hz : z∉tsupport f) : kernel f g t z=0 := by
  unfold kernel densityPair
  rw [image_eq_zero_of_notMem_tsupport hz,map_zero,inner_zero_left]

/-- Compact domination is paid in the original configuration measure, before Hilbert differentiation. -/
theorem weak_flow_derivative (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sourcePair f (coreFlow s g))
      (Complex.I*sourcePair f (coreFlow t (dilation g))) t := by
  let F := kernel f g
  let F' : ℝ → SourceCoordinateSlice → ℂ := fun s z => Complex.I*kernel f (dilation g) s z
  have hcont : Continuous (fun p : ℝ×SourceCoordinateSlice => F' p.1 p.2) :=
    (kernel_continuous f (dilation g)).const_mul Complex.I
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod f.hasCompactSupport).exists_bound_of_continuousOn
    (hcont.continuousOn : ContinuousOn (fun p : ℝ×SourceCoordinateSlice => F' p.1 p.2)
      (Icc (t-1) (t+1)×ˢtsupport f))
  let bound : SourceCoordinateSlice → ℝ := (tsupport f).indicator (fun _ => C)
  have hbound : Integrable bound GaussHistoryHilbert.configurationMeasure :=
    (integrableOn_const (μ := GaussHistoryHilbert.configurationMeasure) (C := C) f.hasCompactSupport.measure_ne_top).integrable_indicator
      (isClosed_tsupport f).measurableSet
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := GaussHistoryHilbert.configurationMeasure) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (Filter.Eventually.of_forall (fun s => (densityPair_integrable f (coreFlow s g)).aestronglyMeasurable))
    (densityPair_integrable f (coreFlow t g))
    ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => by
      intro s hs
      by_cases hz : z∈tsupport f
      · change ‖F' s z‖≤(tsupport f).indicator (fun _ => C) z
        rw [Set.indicator_of_mem hz]
        exact hC (s,z) ⟨⟨hs.1.le,hs.2.le⟩,hz⟩
      · change ‖Complex.I*kernel f (dilation g) s z‖≤(tsupport f).indicator (fun _ => C) z
        rw [kernel_zero f (dilation g) s z hz,Set.indicator_of_notMem hz,mul_zero,norm_zero]))
    hbound (Filter.Eventually.of_forall (fun z s _ => kernel_derivative f g z s))
  have he : (fun s => ∫ z, F s z ∂GaussHistoryHilbert.configurationMeasure)=(fun s => sourcePair f (coreFlow s g)) := by
    funext s
    exact (sourcePair_integral f (coreFlow s g)).symm
  rw [he] at hd
  have hvalue : (∫ z, F' t z ∂GaussHistoryHilbert.configurationMeasure)=Complex.I*sourcePair f (coreFlow t (dilation g)) := by
    rw [sourcePair_integral]
    exact integral_const_mul _ _
  rw [hvalue] at hd
  exact hd.2

theorem pair_difference_bound (f g : QuantumTest) (s t : ℝ) :
    ‖sourcePair f (coreFlow t g)-sourcePair f (coreFlow s g)‖≤
      (‖embed f‖*‖embed (dilation g)‖)*‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (weak_flow_derivative f g u).hasDerivWithinAt)
    (fun u _ => ?_) convex_univ (mem_univ s) (mem_univ t)
  rw [norm_mul,Complex.norm_I,one_mul]
  change ‖inner ℂ (embed f) (embed (coreFlow u (dilation g)))‖≤_
  exact (norm_inner_le_norm _ _).trans_eq (by rw [coreFlow_norm])

theorem core_difference_bound (f : QuantumTest) (s t : ℝ) :
    ‖embed (coreFlow t f)-embed (coreFlow s f)‖≤‖embed (dilation f)‖*‖t-s‖ := by
  let q := coreFlow t f-coreFlow s f
  have h := pair_difference_bound q f s t
  change ‖inner ℂ (embed q) (embed (coreFlow t f))-inner ℂ (embed q) (embed (coreFlow s f))‖≤_ at h
  rw [←inner_sub_right,←map_sub] at h
  change ‖inner ℂ (embed q) (embed q)‖≤(‖embed q‖*‖embed (dilation f)‖)*‖t-s‖ at h
  rw [←inner_self_re_eq_norm,inner_self_eq_norm_sq] at h
  have hnonneg : 0≤‖embed (dilation f)‖*‖t-s‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hn : ‖embed q‖≤‖embed (dilation f)‖*‖t-s‖ := by
    nlinarith [norm_nonneg (embed q)]
  simpa only [q,map_sub] using hn

theorem core_continuous (f : QuantumTest) : Continuous (fun t : ℝ => embed (coreFlow t f)) := by
  have h : LipschitzWith ‖embed (dilation f)‖₊ (fun t : ℝ => embed (coreFlow t f)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [dist_eq_norm,coe_nnnorm] using core_difference_bound f t s
  exact h.continuous

private theorem velocity_continuous (f : QuantumTest) :
    Continuous (fun t : ℝ => Complex.I • embed (coreFlow t (dilation f))) :=
  (core_continuous (dilation f)).const_smul Complex.I

theorem core_integral (f : QuantumTest) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, Complex.I • embed (coreFlow s (dilation f)))=
      embed (coreFlow t f)-embed f := by
  apply ext_inner_left ℂ
  intro x
  refine embed_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  have hi := (velocity_continuous f).intervalIntegrable (μ := MeasureTheory.volume) 0 t
  have hmap := (innerSL ℂ (embed g)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t, inner ℂ (embed g)
      (Complex.I • embed (coreFlow s (dilation f))))=
    inner ℂ (embed g) (∫ s in (0 : ℝ)..t, Complex.I • embed (coreFlow s (dilation f))) at hmap
  rw [←hmap,inner_sub_right]
  simp only [inner_smul_right]
  change (∫ s in (0 : ℝ)..t, Complex.I*sourcePair g (coreFlow s (dilation f)))=
    sourcePair g (coreFlow t f)-sourcePair g f
  have hc : Continuous (fun s : ℝ => Complex.I*sourcePair g (coreFlow s (dilation f))) := by
    exact (continuous_const.inner (core_continuous (dilation f))).const_mul Complex.I
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => weak_flow_derivative g f s) (hc.intervalIntegrable 0 t)
  simpa only [coreFlow_zero] using! h

theorem strong_core_derivative (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => embed (coreFlow s f))
      (Complex.I • embed (coreFlow t (dilation f))) t := by
  have hc := velocity_continuous f
  let : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun s : ℝ => embed (coreFlow s f))=
      (fun s => embed f+∫ u in (0 : ℝ)..s, Complex.I • embed (coreFlow u (dilation f))) := by
    funext s
    rw [core_integral]
    abel
  rw [he]
  exact h.const_add (embed f)

theorem hilbert_strong_continuous (x : H) : Continuous (fun t : ℝ => hilbertFlow t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨f,hf⟩ := embed_dense.exists_dist_lt x (show 0<ε/4 by positivity)
  obtain ⟨δ,hδ,hδt⟩ := Metric.continuousAt_iff.mp (core_continuous f).continuousAt
    (ε/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s hs
  have hm : dist (hilbertFlow s (embed f)) (hilbertFlow t (embed f))<ε/2 := by
    rw [hilbertFlow_on_core,hilbertFlow_on_core]
    exact hδt hs
  have h₁ := dist_triangle (hilbertFlow s x) (hilbertFlow s (embed f)) (hilbertFlow t x)
  have h₂ := dist_triangle (hilbertFlow s (embed f)) (hilbertFlow t (embed f)) (hilbertFlow t x)
  rw [(hilbertFlow s).isometry.dist_eq] at h₁
  rw [(hilbertFlow t).isometry.dist_eq,dist_comm (embed f) x] at h₂
  linarith

def strongJet (n : ℕ) (f : QuantumTest) (t : ℝ) : H :=
  Complex.I^n • embed (coreFlow t ((dilation^n) f))

theorem strong_jet_zero (f : QuantumTest) (t : ℝ) :
    strongJet 0 f t=embed (coreFlow t f) := by simp [strongJet]

theorem strong_jet_derivative (n : ℕ) (f : QuantumTest) (t : ℝ) :
    HasDerivAt (strongJet n f) (strongJet (n+1) f t) t := by
  have h := (strong_core_derivative ((dilation^n) f) t).const_smul (Complex.I^n)
  have hd : (dilation^(n+1)) f=dilation ((dilation^n) f) := by rw [pow_succ']; rfl
  change HasDerivAt (fun s => Complex.I^n • embed (coreFlow s ((dilation^n) f)))
    (Complex.I^(n+1) • embed (coreFlow t ((dilation^(n+1)) f))) t
  rw [hd,pow_succ Complex.I n]
  simpa only [smul_smul,Pi.smul_apply] using! h

theorem strong_jet_norm (n : ℕ) (f : QuantumTest) (t : ℝ) :
    ‖strongJet n f t‖=‖embed ((dilation^n) f)‖ := by
  rw [strongJet,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul,coreFlow_norm]

theorem strong_jet_difference_bound (n : ℕ) (f : QuantumTest) (s t : ℝ) :
    ‖strongJet n f t-strongJet n f s‖≤‖embed ((dilation^(n+1)) f)‖*‖t-s‖ := by
  have hd : (dilation^(n+1)) f=dilation ((dilation^n) f) := by rw [pow_succ']; rfl
  simp only [strongJet,←smul_sub,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul,hd]
  exact core_difference_bound ((dilation^n) f) s t

theorem finite_profile_derivative (F : GaussUnitaryHistory.Index) (z : ℂ)
    (n : ℕ) (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s => FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f s))
      (FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet (n+1) f t)) t := by
  exact ((FullYSourceResolventGraphSplice.finiteResolvent F z).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t (strong_jet_derivative n f t)

theorem finite_profile_bound (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0)
    (n : ℕ) (f : QuantumTest) (t : ℝ) :
    ‖FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f t)‖≤
      (1/|z.im|)*‖embed ((dilation^n) f)‖ := by
  have h := ((FullYSourceResolventGraphSplice.finiteResolvent F z).le_opNorm (strongJet n f t)).trans
    (mul_le_mul_of_nonneg_right (FullYSourceResolventGraphSplice.finite_resolvent_norm F z hz) (norm_nonneg _))
  simpa only [strong_jet_norm] using! h

theorem finite_profile_difference_bound (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0)
    (n : ℕ) (f : QuantumTest) (s t : ℝ) :
    ‖FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f t)-
      FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f s)‖≤
      (1/|z.im|)*‖embed ((dilation^(n+1)) f)‖*‖t-s‖ := by
  rw [←map_sub]
  have h := ((FullYSourceResolventGraphSplice.finiteResolvent F z).le_opNorm
    (strongJet n f t-strongJet n f s)).trans
    (mul_le_mul_of_nonneg_right (FullYSourceResolventGraphSplice.finite_resolvent_norm F z hz) (norm_nonneg _))
  exact h.trans ((mul_le_mul_of_nonneg_left (strong_jet_difference_bound n f s t)
    (by positivity : 0≤1/|z.im|)).trans_eq (by ring))

end LowEnergy.SourceCoframeStrongJet
