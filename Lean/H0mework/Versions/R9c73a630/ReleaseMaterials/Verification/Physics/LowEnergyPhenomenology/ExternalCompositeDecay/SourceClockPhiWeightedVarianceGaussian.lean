import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeHamiltonianPower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceCoframeVolume
open SourceClockPhiCorrectedGaussianPair SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext MeasureTheory Filter ProbabilityTheory
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev G(t:ℝ):End:=sourceGain (Real.sqrt t)
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ2:=γ.prod γ
attribute [local irreducible] sourcePair embed correctedCompleteCore
private theorem gain_square(t:ℝ)(ht:0<t)(z:physicalChart):
    (gainProfile (Real.sqrt t) z.val)^2=(forwardRatio t z.val)^(1/3:ℝ):=by
  have hr:=forward_ratio_pos t ht.le z
  unfold gainProfile
  rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 1
  norm_num
private theorem gained_weight_product(t:ℝ)(ht:0<t)(p q r s:ℝ)(x:ℝ×ℝ)(g:QuantumTest):
    W t ht p q x (G t (G t (W t ht r s x g)))=W t ht (p+r+1/3) (q+s) x g:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change ((((forwardRatio t z)^p*Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) •
      ((gainProfile (Real.sqrt t) z:ℂ) • ((gainProfile (Real.sqrt t) z:ℂ) •
        ((((forwardRatio t z)^r*Real.exp (s*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • g z))))=
      ((((forwardRatio t z)^(p+r+1/3)*Real.exp ((q+s)*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • g z)
    simp only[smul_smul,←Complex.ofReal_mul]
    have he:(forwardRatio t z)^p*Real.exp (q*correctedCoefficient t x.1 x.2 z)*
        (gainProfile (Real.sqrt t) z*(gainProfile (Real.sqrt t) z*
          ((forwardRatio t z)^r*Real.exp (s*correctedCoefficient t x.1 x.2 z))))=
        (forwardRatio t z)^(p+r+1/3)*Real.exp ((q+s)*correctedCoefficient t x.1 x.2 z):=by
      calc
        _=(forwardRatio t z)^p*(forwardRatio t z)^r*(gainProfile (Real.sqrt t) z)^2*
          (Real.exp (q*correctedCoefficient t x.1 x.2 z)*Real.exp (s*correctedCoefficient t x.1 x.2 z)):=by ring
        _=_:=by
          rw [gain_square t ht ⟨z,hz⟩,←Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩),
            ←Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩),←Real.exp_add]
          congr 2
          ring
    rw [he]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

theorem actual_gained_profile_pair(t:ℝ)(ht:0<t)(p q r s:ℝ)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (G t (W t ht p q x f)) (G t (W t ht r s x g))=
      sourcePair f (W t ht (p+r+1/3) (q+s) x g):=by
  have hG:sourcePair (G t (W t ht p q x f)) (G t (W t ht r s x g))=
      sourcePair (W t ht p q x f) (G t (G t (W t ht r s x g))):=(multiply_pair _ _ _ _).symm
  have hW:sourcePair (W t ht p q x f) (G t (G t (W t ht r s x g)))=
      sourcePair f (W t ht p q x (G t (G t (W t ht r s x g)))):=(multiply_pair _ _ _ _).symm
  rw [hG,hW,gained_weight_product]

/-- Every ordered native/profile pair has its own genuine two-Gaussian integral and exact
finite source power. This includes the diagonal norm-square required by full-H0 variance. -/
theorem actual_gained_profile_pair_gaussian(t:ℝ)(ht:0<t)(p q r s:ℝ)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G t (W t ht p q x f)) (G t (W t ht r s x g))) γ2 ∧
    (∫x:ℝ×ℝ,sourcePair (G t (W t ht p q x f)) (G t (W t ht r s x g)) ∂γ2)=
      sourcePair f (gaussianProfileWeight t ht (p+r+1/3+(q+s)*(q+s-3)/18) g):=by
  simp_rw [actual_gained_profile_pair]
  exact actual_corrected_gaussian_weighted_source_pair t ht (p+r+1/3) (q+s) f g

/-- All 121 ordered native rows of the actual returned Hamiltonian have source-generated
Gaussian L1 and means, before they are joined to the full coframe rows. -/
theorem actual_native_variance_row_gaussian(t:ℝ)(ht:0<t)(i j:Fin 11)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair
      (G t (W t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) x (nativeVarianceRow i f)))
      (G t (W t ht (nativeVariancePower j-1/3) (nativeVarianceDegree j) x (nativeVarianceRow j g)))) γ2 ∧
    (∫x:ℝ×ℝ,sourcePair
      (G t (W t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i) x (nativeVarianceRow i f)))
      (G t (W t ht (nativeVariancePower j-1/3) (nativeVarianceDegree j) x (nativeVarianceRow j g))) ∂γ2)=
      sourcePair (nativeVarianceRow i f)
        (gaussianProfileWeight t ht (nativeVariancePower i+nativeVariancePower j-1/3+
          (nativeVarianceDegree i+nativeVarianceDegree j)*(nativeVarianceDegree i+nativeVarianceDegree j-3)/18)
          (nativeVarianceRow j g)):=by
  have h:=actual_gained_profile_pair_gaussian t ht (nativeVariancePower i-1/3) (nativeVarianceDegree i)
    (nativeVariancePower j-1/3) (nativeVarianceDegree j) (nativeVarianceRow i f) (nativeVarianceRow j g)
  have he:(nativeVariancePower i-1/3)+(nativeVariancePower j-1/3)+1/3=
      nativeVariancePower i+nativeVariancePower j-1/3:=by ring
  rw [he] at h
  exact h

private theorem weight_product(t:ℝ)(ht:0<t)(p q r s:ℝ)(x:ℝ×ℝ)(g:QuantumTest):
    W t ht p q x (W t ht r s x g)=W t ht (p+r) (q+s) x g:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change ((((forwardRatio t z)^p*Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) •
      ((((forwardRatio t z)^r*Real.exp (s*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • g z))=
      ((((forwardRatio t z)^(p+r)*Real.exp ((q+s)*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • g z)
    rw [smul_smul,←Complex.ofReal_mul]
    congr 2
    rw [Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩),add_mul,Real.exp_add]
    ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem weight_square(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ)(g:QuantumTest):
    ‖embed (W t ht p q x g)‖^2=(sourcePair g (W t ht (p+p) (q+q) x g)).re:=by
  rw [←pair_norm]
  have h:sourcePair (W t ht p q x g) (W t ht p q x g)=
      sourcePair g (W t ht p q x (W t ht p q x g)):=(multiply_pair _ _ _ _).symm
  rw [h,weight_product]

/-- Source exponential moments internally give L2 of every weighted original pair.
This supplies the mixed native/coframe Gaussian terms without an external moment budget. -/
theorem actual_profile_pair_memLp_two(t:ℝ)(ht:0<t)(p q:ℝ)(f g:QuantumTest):
    MemLp (fun x:ℝ×ℝ=>sourcePair f (W t ht p q x g)) 2 γ2:=by
  have hi:=(actual_corrected_gaussian_weighted_source_pair t ht p q f g).1
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  have hs:=((actual_corrected_gaussian_weighted_source_pair t ht (p+p) (q+q) g g).1.re).const_mul (‖embed f‖^2)
  apply hs.mono' (hi.aestronglyMeasurable.norm.pow 2)
  exact Eventually.of_forall (fun x=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),RCLike.re_eq_complex_re,←weight_square]
    have h:‖sourcePair f (W t ht p q x g)‖≤‖embed f‖*‖embed (W t ht p q x g)‖:=by
      simpa only[sourcePair] using norm_inner_le_norm (𝕜:=ℂ) (embed f) (embed (W t ht p q x g))
    change ‖sourcePair f (W t ht p q x g)‖^2≤‖embed f‖^2*‖embed (W t ht p q x g)‖^2
    nlinarith [norm_nonneg (sourcePair f (W t ht p q x g)),norm_nonneg (embed f),norm_nonneg (embed (W t ht p q x g))])
private theorem gaussian_power_integrable(k:ℕ):Integrable (fun x:ℝ=>x^k) γ:=by
  have h:=(memLp_id_gaussianReal' (μ:=0) (v:=1) (k:ENNReal) (by finiteness)).integrable_norm_pow'
  apply h.mono' (by fun_prop)
  exact Eventually.of_forall (fun x=>by simp only[norm_pow,id_eq,le_refl])
private theorem noiseQuadratic_l2(i:QuadraticIndex):MemLp (fun x:ℝ×ℝ=>(noiseQuadratic i x:ℂ)) 2 γ2:=by
  let a:ℕ:=(if i.1=1 then 1 else 0)+(if i.2=1 then 1 else 0)
  let b:ℕ:=(if i.1=2 then 1 else 0)+(if i.2=2 then 1 else 0)
  have he(x:ℝ×ℝ):noiseQuadratic i x=x.1^a*x.2^b:=by
    change (x.1^(if i.1=1 then 1 else 0)*x.2^(if i.1=2 then 1 else 0))*
      (x.1^(if i.2=1 then 1 else 0)*x.2^(if i.2=2 then 1 else 0))=x.1^a*x.2^b
    simp only[a,b,pow_add]
    ring
  have hm:AEStronglyMeasurable (fun x:ℝ×ℝ=>(noiseQuadratic i x:ℂ)) γ2:=by
    simp_rw [he]
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have h:=(gaussian_power_integrable (a*2)).mul_prod (gaussian_power_integrable (b*2))
  convert h using 1
  funext x
  simp only[he,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,←pow_mul]

/-- The polynomial coframe rows and exponential native rows have their actual joint
Gaussian L1; no factor is treated as uniformly bounded. -/
theorem actual_quadratic_profile_pair_integrable(t:ℝ)(ht:0<t)(p q:ℝ)(i:QuadraticIndex)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(noiseQuadratic i x:ℂ)*sourcePair f (W t ht p q x g)) γ2:=by
  exact (noiseQuadratic_l2 i).integrable_mul (actual_profile_pair_memLp_two t ht p q f g)
end LowEnergy.FirstCurrentWholeVariance
