import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseClockPolynomialPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeCarrierElectric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiWholeSignedWorkIntegrable SourceClockPhiForwardNativeReturn SourceClockPhiHeatLocalNativeGaussian
open SourceScalarShiftedBulk SourceScalarDoubleCurrent SourceResolventBandLimit SourceLocalizedInverseFormPayment
open FirstCurrentWholeCarrier FirstCurrentGeometricPayer FirstCurrentJointBudget FirstCurrentElectricSuccessor
open ClockPhiHeatCorrectedCovarianceSource MeasureTheory
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev X:End:=weightedElectricCurrent
private abbrev U:End:=inverseVolumeAction
private abbrev M:End:=matchedTester
private abbrev D:End:=combinedGenerator
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed normalizedState normalizedForcing correctedCompleteCore
  wholeStep wholeGraphPrice wholeNormPrice wholeSlope wholeCurvature frequencyState wholeSourceNext
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private theorem pair_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (frequencyState half advanced m ell F g q))
      (R (frequencyState half advanced m ell F g q))):=
  by simpa only [frequencyState] using actual_normalized_pair_integrable _ (frequency_positive half) advanced m ell F g L R
private theorem square_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (frequencyState half advanced m ell F g q))‖^2):=by
  have h:=(pair_frequency half advanced m ell F g L L).re
  simpa only [sourcePair,RCLike.re_eq_complex_re,inner_self_eq_norm_sq] using h
private theorem price_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>scalarClockSourcePrice (L (frequencyState half advanced m ell F g q))):=by
  let hi(A:End):=square_frequency half advanced m ell F g (A*L)
  have h(i:Fin 4):Integrable (fun q:ℝ=>scalarClockWeight i*
      (54*(‖embed (M (L (frequencyState half advanced m ell F g q)))‖^2+
        ‖embed (clockSquareCap (U (scalarClockWord i (L (frequencyState half advanced m ell F g q)))))‖^2)/2+
      (18*|scalarClockNoiseDegree i|)*(‖embed (D (L (frequencyState half advanced m ell F g q)))‖^2+
        ‖embed (clockSquareCap (U (U (scalarClockWord i (L (frequencyState half advanced m ell F g q))))))‖^2)/2)):=
    ((((hi M).add (hi (clockSquareCap*U*scalarClockWord i))).const_mul 54).div_const 2 |>.add
      ((((hi D).add (hi (clockSquareCap*U*U*scalarClockWord i))).const_mul (18*|scalarClockNoiseDegree i|)).div_const 2)).const_mul _
  exact integrable_finsetSum Finset.univ (fun i _=>h i)
private theorem slope_frequency(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>scalarReverseClockSlope t ht (L (frequencyState half advanced m ell F g q))
      (L (frequencyState half advanced m ell F g q))):=by
  change Integrable (fun q:ℝ=>∑i:Fin 4,(![-8,8,-8,2]:Fin 4→ℂ) i*
    ((-54:ℂ)*sourcePair (M (L (frequencyState half advanced m ell F g q)))
      (gaussianProfileWeight t ht ((![-2/3,4/3,4/3,4/3]:Fin 4→ℝ) i+
        scalarClockNoiseDegree i*(scalarClockNoiseDegree i-3)/18)
          (forwardUAction t ht.le (scalarClockWord i (L (frequencyState half advanced m ell F g q)))))+
      (18*scalarClockNoiseDegree i:ℂ)*sourcePair (D (L (frequencyState half advanced m ell F g q)))
        (U (gaussianProfileWeight t ht ((![-2/3,4/3,4/3,4/3]:Fin 4→ℝ) i+
          scalarClockNoiseDegree i*(scalarClockNoiseDegree i-3)/18)
            (forwardUAction t ht.le (scalarClockWord i (L (frequencyState half advanced m ell F g q))))))))
  apply integrable_finsetSum Finset.univ;intro i _
  let T:End:=gaussianProfileWeight t ht ((![-2/3,4/3,4/3,4/3]:Fin 4→ℝ) i+
      scalarClockNoiseDegree i*(scalarClockNoiseDegree i-3)/18)*forwardUAction t ht.le*scalarClockWord i*L
  exact (((pair_frequency half advanced m ell F g (M*L) T).const_mul (-54:ℂ)).add
    ((pair_frequency half advanced m ell F g (D*L) (U*T)).const_mul (18*scalarClockNoiseDegree i:ℂ))).const_mul _
private theorem cap_small(A C W P:ℝ)(hW:0≤W)(hP:0≤P):
    |(-A/(2*(|C|+1)))*(W/((|A|+1)*(W+P+|A|+|C|+1)))|≤1/2:=by
  have hD:0<(|A|+1)*(W+P+|A|+|C|+1):=by positivity
  have hE:0<2*(|C|+1):=by positivity
  have hp:W≤W+P+|A|+|C|+1:=by linarith [abs_nonneg A,abs_nonneg C]
  have hq:W/((|A|+1)*(W+P+|A|+|C|+1))≤1/(|A|+1):=by
    apply (div_le_div_iff₀ hD (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity:0≤|A|+1)]
  rw [abs_mul,abs_div,abs_neg,abs_of_pos hE,abs_div,abs_of_nonneg hW,abs_of_pos hD]
  calc
    _≤(|A|/(2*(|C|+1)))*(1/(|A|+1)):=mul_le_mul_of_nonneg_left hq (by positivity)
    _≤1/2:=by
      field_simp [ne_of_gt (show 0 < |A|+1 by positivity),ne_of_gt (show 0 < |C|+1 by positivity)]
      nlinarith [mul_nonneg (abs_nonneg A) (abs_nonneg C),abs_nonneg C]
private theorem whole_step_small(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    |wholeStep t ht half advanced m ell F g|≤1:=by
  have hW:0≤wholeNormPrice half advanced m ell F g:=by unfold wholeNormPrice;exact integral_nonneg (fun _=>sq_nonneg _)
  have hP:0≤wholeGraphPrice half advanced m ell F g:=by
    unfold wholeGraphPrice
    apply integral_nonneg;intro q
    unfold wholeGraphDensity comparisonEnergy
    positivity
  have h:=cap_small (wholeSlope t ht half advanced m ell F g) (wholeCurvature t ht half advanced m ell F g)
    (wholeNormPrice half advanced m ell F g) (wholeGraphPrice half advanced m ell F g) hW hP
  have hh:|wholeStep t ht half advanced m ell F g|≤1/2:=by
    simpa only [wholeStep,wholeFraction] using h
  linarith
private theorem word_square_add(h:ℝ)(hh:|h|≤1)(f g:QuantumTest)(A:End):
    ‖embed (A (f+(h:ℂ) • g))‖^2≤2*(‖embed (A f)‖^2+‖embed (A g)‖^2):=by
  have hn:‖embed (A (f+(h:ℂ) • g))‖≤‖embed (A f)‖+‖embed (A g)‖:=by
    simp only [map_add,map_smul]
    apply (norm_add_le _ _).trans
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [norm_nonneg (embed (A g))]
  nlinarith [sq_nonneg (‖embed (A f)‖-‖embed (A g)‖),norm_nonneg (embed (A (f+(h:ℂ) • g))),norm_nonneg (embed (A f)),norm_nonneg (embed (A g))]
private theorem price_add(h:ℝ)(hh:|h|≤1)(f g:QuantumTest):
    scalarClockSourcePrice (f+(h:ℂ) • g)≤2*(scalarClockSourcePrice f+scalarClockSourcePrice g):=by
  unfold scalarClockSourcePrice
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum;intro i _
  have hw:0≤ scalarClockWeight i:=by fin_cases i <;> norm_num [scalarClockWeight,Matrix.cons_val]
  have h1:=word_square_add h hh f g M
  have h2:=word_square_add h hh f g D
  have h3:=word_square_add h hh f g (clockSquareCap*U*scalarClockWord i)
  have h4:=word_square_add h hh f g (clockSquareCap*U*U*scalarClockWord i)
  simp only [Module.End.mul_apply] at h3 h4
  have hq:0≤18*|scalarClockNoiseDegree i|:=by positivity
  have hb:=add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h3) (by norm_num:(0:ℝ)≤54))
    (mul_le_mul_of_nonneg_left (add_le_add h2 h4) hq)
  have hx:=mul_le_mul_of_nonneg_left hb hw
  nlinarith only [hx]

def wholeClockWardMean(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):ℂ:=
  let w:=(wholeSourceNext t ht half advanced m ell F g q).1
  ∫x:ℝ×ℝ,sourcePair (bracket reverseNativeClock (correctedCompleteCore t ht x.1 x.2) w)
    (scalarBulkComplete (correctedCompleteCore t ht x.1 x.2 w)) ∂γ.prod γ
def wholeClockSourcePrice(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  2*∫q:ℝ,scalarClockSourcePrice (frequencyState half advanced m ell F g q)+
    scalarClockSourcePrice (X (frequencyState half advanced m ell F g q))
private theorem whole_state(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    (wholeSourceNext t ht half advanced m ell F g q).1=
      wholeSourceMap t ht half advanced m ell F g (frequencyState half advanced m ell F g q):=by
  simp only [wholeSourceNext,wholeSourceMap,electricSourceDirection,Prod.fst_add,Prod.smul_fst,
    LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
private theorem mean_integrable(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (wholeClockWardMean t ht half advanced m ell F g):=by
  have h:=(slope_frequency t ht half advanced m ell F g (wholeSourceMap t ht half advanced m ell F g)).const_mul (t:ℂ)
  change Integrable (fun q:ℝ=>wholeClockWardMean t ht half advanced m ell F g q)
  simp only [wholeClockWardMean,(actual_reverse_scalar_clock_payment t ht _ _).2,whole_state]
  exact h

/-- The actual frequency-integrated whole-source update pays the entire clock part of the scalar Ward work from its own fixed polynomial word integrals. -/
theorem actual_whole_reverse_clock_linear_payment(t:ℝ)(ht:0<t)(ht1:t≤1)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (wholeClockWardMean t ht half advanced m ell F g) ∧
    (∫q:ℝ,‖wholeClockWardMean t ht half advanced m ell F g q‖)≤t*wholeClockSourcePrice half advanced m ell F g:=by
  have hi:=mean_integrable t ht half advanced m ell F g
  have h0:=price_frequency half advanced m ell F g (1:End)
  have h1:=price_frequency half advanced m ell F g X
  have hp(q:ℝ):‖wholeClockWardMean t ht half advanced m ell F g q‖≤
      t*(2*(scalarClockSourcePrice (frequencyState half advanced m ell F g q)+
        scalarClockSourcePrice (X (frequencyState half advanced m ell F g q)))):=by
    apply (actual_reverse_scalar_clock_source_bound t ht ht1 _).trans
    apply mul_le_mul_of_nonneg_left _ ht.le
    rw [whole_state]
    change scalarClockSourcePrice (frequencyState half advanced m ell F g q+
      (wholeStep t ht half advanced m ell F g:ℂ) • X (frequencyState half advanced m ell F g q))≤_
    exact price_add _ (whole_step_small t ht half advanced m ell F g) _ _
  have he:=integral_mono hi.norm (((h0.add h1).const_mul 2).const_mul t) hp
  refine ⟨hi,?_⟩
  simpa only [integral_const_mul,wholeClockSourcePrice,Module.End.one_apply,Pi.add_apply] using he

/-- The common small clock is chosen from the same source before both causal branches; no caller norm, endpoint or tail price is needed. -/
theorem actual_whole_reverse_clock_common_payment(ε:ℝ)(hε:0<ε)(half:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    ∃δ:ℝ,0<δ ∧ δ≤1 ∧ ∀advanced:Bool,∀t:ℝ,∀ht:0<t,t≤δ→
      (∫q:ℝ,‖wholeClockWardMean t ht half advanced m ell F g q‖)≤ε:=by
  have hc(a:Bool):0≤wholeClockSourcePrice half a m ell F g:=by
    unfold wholeClockSourcePrice
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun q=>add_nonneg (actual_scalar_clock_source_price_nonnegative _)
      (actual_scalar_clock_source_price_nonnegative _))
  let C:=wholeClockSourcePrice half false m ell F g+wholeClockSourcePrice half true m ell F g
  have hC:0≤C:=add_nonneg (hc false) (hc true)
  refine ⟨min 1 (ε/(C+1)),lt_min (by norm_num) (div_pos hε (by positivity)),min_le_left _ _,?_⟩
  intro advanced t ht hδ
  have ht1:t≤1:=hδ.trans (min_le_left _ _)
  have hs:t*(C+1)≤ε:=(le_div_iff₀ (by positivity:C+1>0)).mp (hδ.trans (min_le_right _ _))
  have ha:wholeClockSourcePrice half advanced m ell F g≤C:=by cases advanced <;> dsimp [C] <;> linarith [hc false,hc true]
  have h:=(actual_whole_reverse_clock_linear_payment t ht ht1 half advanced m ell F g).2
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ha ht.le])
end LowEnergy.ReverseNativeClock
