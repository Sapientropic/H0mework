import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseClockScalarPayment
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussBoundedMultiplier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource
open SourceClockPhiForwardNativeReturn SourceClockPhiCorrectedGaussianPair SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiCoframeForwardCore SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarVirialBulk
open ClockPhiHeatCorrectedCovarianceSource GaussBoundedMultiplier MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed scalarKinetic centeredAction vacuumLinearAction vacuumConstantAction

def scalarClockWord:Fin 4→End:=![scalarKinetic,centeredAction,vacuumLinearAction,vacuumConstantAction]
def scalarClockExponent:Fin 4→ℝ:=![-7/9,17/9,14/9,4/3]
def scalarClockNoiseDegree:Fin 4→ℝ:=![2,-2,-1,0]
def scalarClockWeight:Fin 4→ℝ:=![8,8,8,2]
def clockSquareCap:End:=gaussianProfileWeight 1 (by norm_num) 2

def scalarClockSourcePrice(f:QuantumTest):ℝ:=∑i:Fin 4,scalarClockWeight i*
  (54*(‖embed (M f)‖^2+‖embed (clockSquareCap (U (scalarClockWord i f)))‖^2)/2+
    (18*|scalarClockNoiseDegree i|)*(‖embed (D f)‖^2+
      ‖embed (clockSquareCap (U (U (scalarClockWord i f))))‖^2)/2)

private theorem ratio_bounds(t:ℝ)(ht:0<t)(ht1:t≤1)(z:physicalChart):
    1≤forwardRatio t z.val ∧ forwardRatio t z.val≤forwardRatio 1 z.val:=by
  unfold forwardRatio
  constructor
  · exact (le_div_iff₀ (volume_pos z)).mpr (by linarith)
  · apply (div_le_div_iff_of_pos_right (volume_pos z)).mpr
    linarith
private theorem power_bound(t:ℝ)(ht:0<t)(ht1:t≤1)(p:ℝ)(hp:p≤2)(z:physicalChart):
    0≤(forwardRatio t z.val)^p ∧ (forwardRatio t z.val)^p≤(forwardRatio 1 z.val)^2:=by
  have h:=ratio_bounds t ht ht1 z
  refine ⟨Real.rpow_nonneg (by linarith[h.1]) _,?_⟩
  have h1:(forwardRatio t z.val)^p≤(forwardRatio t z.val)^(2:ℝ):=
    Real.rpow_le_rpow_of_exponent_le h.1 hp
  exact h1.trans (by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith[h.1]) h.2 2)
private theorem weight_norm_bound(t:ℝ)(ht:0<t)(ht1:t≤1)(p:ℝ)(hp:p≤2)(f:QuantumTest):
    ‖embed (gaussianProfileWeight t ht p f)‖≤‖embed (clockSquareCap f)‖:=by
  let a:=gaussianProfileWeight t ht p f
  let b:=clockSquareCap f
  have hpoint(z:SourceCoordinateSlice):RCLike.re (densityPair a a z)≤RCLike.re (densityPair b b z):=by
    by_cases hz:z∈physicalChart
    · have hs:=power_bound t ht ht1 p hp ⟨z,hz⟩
      have hpos:0≤RCLike.re (densityPair f f z):=by
        change 0≤RCLike.re (inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (f z)) (f z))
        rw [weighted_square (fun N=>GaussDensityCore.density N z) (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
        exact sq_nonneg _
      have he:RCLike.re (densityPair (gaussianProfileWeight t ht p f) (gaussianProfileWeight t ht p f) z)=
          ((forwardRatio t z)^p)^2*RCLike.re (densityPair f f z):=by
        simp only [densityPair,gaussianProfileWeight,multiply_apply,map_smul,inner_smul_left,inner_smul_right,
          Complex.conj_ofReal,←mul_assoc]
        rw [←pow_two,←Complex.ofReal_pow]
        exact RCLike.re_ofReal_mul _ _
      have hf:RCLike.re (densityPair b b z)=((forwardRatio 1 z)^(2:ℝ))^2*RCLike.re (densityPair f f z):=by
        simp only [b,clockSquareCap,densityPair,gaussianProfileWeight,multiply_apply,map_smul,
          inner_smul_left,inner_smul_right,Complex.conj_ofReal,←mul_assoc]
        rw [←pow_two,←Complex.ofReal_pow]
        exact RCLike.re_ofReal_mul _ _
      dsimp only [a]
      rw [he,hf,Real.rpow_two]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 2) hpos
    · have h0(g:QuantumTest):g z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (g.tsupport_subset h))
      simp only [densityPair,h0,map_zero,inner_zero_left]
      exact le_refl _
  have hn:‖embed a‖^2≤‖embed b‖^2:=by
    rw [norm_square_integral,norm_square_integral]
    exact integral_mono (densityPair_integrable a a).re (densityPair_integrable b b).re hpoint
  nlinarith [norm_nonneg (embed a),norm_nonneg (embed b)]
private theorem forward_power(t:ℝ)(ht:0<t)(p:ℝ)(f:QuantumTest):
    gaussianProfileWeight t ht p (forwardUAction t ht.le f)=
      gaussianProfileWeight t ht (p-1) (U f):=by
  apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hU:forwardU t z=(forwardRatio t z)⁻¹*reciprocalVolume z:=by
      unfold forwardU forwardRatio reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne']
    change (((forwardRatio t z)^p:ℝ):ℂ) • ((forwardU t z:ℂ) • f z)=
      (((forwardRatio t z)^(p-1):ℝ):ℂ) • ((reciprocalVolume z:ℂ) • f z)
    rw [hU,smul_smul,smul_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,
      Real.rpow_sub hr,Real.rpow_one]
    congr 2
    ring
  · have h0(g:QuantumTest):g z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (g.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem inverse_power(t:ℝ)(ht:0<t)(p:ℝ)(f:QuantumTest):
    U (gaussianProfileWeight t ht p f)=gaussianProfileWeight t ht p (U f):=by
  apply DFunLike.ext;intro z
  change (reciprocalVolume z:ℂ) • (((forwardRatio t z)^p:ℝ):ℂ) • f z=
    (((forwardRatio t z)^p:ℝ):ℂ) • (reciprocalVolume z:ℂ) • f z
  exact smul_comm _ _ _

/-- The small-clock weights are paid by one fixed source polynomial, uniformly on 0<t≤1 and on the entire original core. -/
theorem actual_reverse_clock_source_polynomial(t:ℝ)(ht:0<t)(ht1:t≤1)(i:Fin 4)(f:QuantumTest):
    ‖embed (gaussianProfileWeight t ht (scalarClockExponent i) (forwardUAction t ht.le (scalarClockWord i f)))‖≤
      ‖embed (clockSquareCap (U (scalarClockWord i f)))‖ ∧
    ‖embed (U (gaussianProfileWeight t ht (scalarClockExponent i) (forwardUAction t ht.le (scalarClockWord i f))))‖≤
      ‖embed (clockSquareCap (U (U (scalarClockWord i f))))‖:=by
  have hp:scalarClockExponent i-1≤2:=by fin_cases i <;> norm_num [scalarClockExponent,Matrix.cons_val]
  rw [forward_power,inverse_power]
  exact ⟨weight_norm_bound t ht ht1 _ hp _,weight_norm_bound t ht ht1 _ hp _⟩

private def scalarClockSigned:Fin 4→ℂ:=![-8,8,-8,2]
private theorem scalar_slope_return(t:ℝ)(ht:0<t)(f:QuantumTest):
    scalarReverseClockSlope t ht f f=∑i:Fin 4,scalarClockSigned i*((-54:ℂ)*sourcePair (M f)
      (gaussianProfileWeight t ht (scalarClockExponent i) (forwardUAction t ht.le (scalarClockWord i f)))+
      (18*scalarClockNoiseDegree i:ℂ)*sourcePair (D f)
        (U (gaussianProfileWeight t ht (scalarClockExponent i) (forwardUAction t ht.le (scalarClockWord i f))))):=by
  change (∑i:Fin 4,(![-8,8,-8,2]:Fin 4→ℂ) i*((-54:ℂ)*sourcePair (M f)
    (gaussianProfileWeight t ht ((![-2/3,4/3,4/3,4/3]:Fin 4→ℝ) i+
      scalarClockNoiseDegree i*(scalarClockNoiseDegree i-3)/18) (forwardUAction t ht.le (scalarClockWord i f)))+
    (18*scalarClockNoiseDegree i:ℂ)*sourcePair (D f)
      (U (gaussianProfileWeight t ht ((![-2/3,4/3,4/3,4/3]:Fin 4→ℝ) i+
        scalarClockNoiseDegree i*(scalarClockNoiseDegree i-3)/18) (forwardUAction t ht.le (scalarClockWord i f))))))=_
  apply Finset.sum_congr rfl;intro i _
  fin_cases i <;> norm_num [scalarClockSigned,scalarClockExponent,scalarClockNoiseDegree,Matrix.cons_val]
private theorem pair_bound(f g:QuantumTest):‖sourcePair f g‖≤‖embed f‖*‖embed g‖:=by
  simpa only [sourcePair] using norm_inner_le_norm (𝕜:=ℂ) (embed f) (embed g)
private theorem scalar_slope_bound(t:ℝ)(ht:0<t)(ht1:t≤1)(f:QuantumTest):
    ‖scalarReverseClockSlope t ht f f‖≤ scalarClockSourcePrice f:=by
  rw [scalar_slope_return]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum;intro i _
  have h:=actual_reverse_clock_source_polynomial t ht ht1 i f
  let a:=gaussianProfileWeight t ht (scalarClockExponent i) (forwardUAction t ht.le (scalarClockWord i f))
  let c:=clockSquareCap (U (scalarClockWord i f))
  let d:=clockSquareCap (U (U (scalarClockWord i f)))
  have h1:‖sourcePair (M f) a‖≤(‖embed (M f)‖^2+‖embed c‖^2)/2:=by
    have hp:=(pair_bound (M f) a).trans (mul_le_mul_of_nonneg_left h.1 (norm_nonneg _))
    nlinarith [sq_nonneg (‖embed (M f)‖-‖embed c‖)]
  have h2:‖sourcePair (D f) (U a)‖≤(‖embed (D f)‖^2+‖embed d‖^2)/2:=by
    have hp:=(pair_bound (D f) (U a)).trans (mul_le_mul_of_nonneg_left h.2 (norm_nonneg _))
    nlinarith [sq_nonneg (‖embed (D f)‖-‖embed d‖)]
  have hc:‖scalarClockSigned i‖=scalarClockWeight i:=by
    fin_cases i <;> norm_num [scalarClockSigned,scalarClockWeight,Matrix.cons_val]
  have hn:0≤ scalarClockWeight i:=by fin_cases i <;> norm_num [scalarClockWeight,Matrix.cons_val]
  have hq:‖(18*scalarClockNoiseDegree i:ℂ)‖=18*|scalarClockNoiseDegree i|:=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num
  rw [norm_mul,hc]
  apply mul_le_mul_of_nonneg_left _ hn
  have hab:=norm_add_le ((-54:ℂ)*sourcePair (M f) a)
    ((18*scalarClockNoiseDegree i:ℂ)*sourcePair (D f) (U a))
  rw [norm_mul,norm_mul,hq] at hab
  norm_num at hab
  dsimp only [a,c,d] at h1 h2 hab
  simp only [neg_mul] at hab ⊢
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num:(0:ℝ)≤18) (abs_nonneg (scalarClockNoiseDegree i)))]

theorem actual_scalar_clock_source_price_nonnegative(f:QuantumTest):0≤ scalarClockSourcePrice f:=by
  apply Finset.sum_nonneg;intro i _
  have hn:0≤ scalarClockWeight i:=by fin_cases i <;> norm_num [scalarClockWeight,Matrix.cons_val]
  positivity

/-- The complete original scalar clock-Ward pair consumes the fixed polynomial source price; its small factor is generated before any frequency cutoff or causal choice. -/
theorem actual_reverse_scalar_clock_source_bound(t:ℝ)(ht:0<t)(ht1:t≤1)(f:QuantumTest):
    ‖∫x:ℝ×ℝ,sourcePair (bracket reverseNativeClock (correctedCompleteCore t ht x.1 x.2) f)
      (scalarBulkComplete (correctedCompleteCore t ht x.1 x.2 f)) ∂γ.prod γ‖≤t*scalarClockSourcePrice f:=by
  rw [(actual_reverse_scalar_clock_payment t ht f f).2,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left (scalar_slope_bound t ht ht1 f) ht.le
end LowEnergy.ReverseNativeClock
