import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarCausalPositiveCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFixedSourceFrequencyPair
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentRadialDifferenceDissipation
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarInverseNativeEnergy
open SourceScalarDoubleCurrent SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceResolventBandLimit MeasureTheory Filter
open ScalarCausalFrequencyMoment InputForceFrequencyPayment
open scoped Topology InnerProductSpace
variable {ι : Type*} [Fintype ι]
attribute [local irreducible] sourcePair embed

private def coefficient (v : ι → QuantumTest) (i j : ι) : ℂ := sourcePair (v i) (v j)
private def timeGram (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, Complex.exp (-causalGap advanced μ (freq i) (freq j)*(t : ℂ))*coefficient v i j
private def doubleGram (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) : ℂ :=
  ∑ i, ∑ j, (causalGap advanced μ (freq i) (freq j))⁻¹ ^ 2*coefficient v i j

private theorem gap_re (advanced : Bool) (μ a b : ℝ) : (causalGap advanced μ a b).re = 2*μ := by
  cases advanced <;> simp [causalGap, gap]
private theorem gap_nonzero (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) : causalGap advanced μ a b ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  rw [gap_re] at hr
  simp only [Complex.zero_re] at hr
  linarith
private theorem decay_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-causalGap advanced μ a b*(t : ℂ))) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  rw [Complex.neg_re, gap_re]
  linarith
private theorem decay_integral (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ t : ℝ in Set.Ioi 0, Complex.exp (-causalGap advanced μ a b*(t : ℂ))) = (causalGap advanced μ a b)⁻¹ := by
  have hn : (-causalGap advanced μ a b).re < 0 := by rw [Complex.neg_re, gap_re]; linarith
  rw [integral_exp_mul_complex_Ioi hn 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg, one_div]
private theorem time_gram_integrable (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) :
    IntegrableOn (timeGram advanced μ freq v) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable advanced μ (freq i) (freq j) hμ).mul_const _))
private theorem time_factor (advanced : Bool) (μ a b t : ℝ) :
    Complex.exp (-causalGap advanced μ a b*(t : ℂ)) =
      (Real.exp (-2*μ*t) : ℂ)*
        star (Complex.exp (-((causalDirection advanced : ℝ) : ℂ)*Complex.I*(a : ℂ)*(t : ℂ)))*
        Complex.exp (-((causalDirection advanced : ℝ) : ℂ)*Complex.I*(b : ℂ)*(t : ℂ)) := by
  cases advanced <;> simp only [causalGap, causalDirection, Bool.false_eq_true, ite_false, ite_true, gap]
  all_goals
    simp only [Complex.star_def, ← Complex.exp_conj, Complex.ofReal_exp,
      map_add, map_mul, map_sub, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
private theorem time_gram_value (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (t : ℝ) :
    (timeGram advanced μ freq v t).re = Real.exp (-2*μ*t)*‖embed (scalarCausalWave advanced freq v t)‖^2 := by
  have hs : sourcePair (scalarCausalWave advanced freq v t) (scalarCausalWave advanced freq v t) =
      ∑ i, ∑ j, star (Complex.exp (-((causalDirection advanced : ℝ) : ℂ)*Complex.I*(freq i : ℂ)*(t : ℂ)))*
        Complex.exp (-((causalDirection advanced : ℝ) : ℂ)*Complex.I*(freq j : ℂ)*(t : ℂ))*coefficient v i j := by
    simp only [scalarCausalWave, coefficient, sourcePair, map_sum, map_smul,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ht : timeGram advanced μ freq v t = (Real.exp (-2*μ*t) : ℂ)*
      sourcePair (scalarCausalWave advanced freq v t) (scalarCausalWave advanced freq v t) := by
    unfold timeGram
    simp_rw [time_factor]
    rw [hs]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ht, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed (scalarCausalWave advanced freq v t))
private theorem shifted_decay_integral (advanced : Bool) (μ a b t : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-causalGap advanced μ a b*((t+u : ℝ) : ℂ))) (Set.Ioi 0) ∧
    (∫ u : ℝ in Set.Ioi 0, Complex.exp (-causalGap advanced μ a b*((t+u : ℝ) : ℂ))) =
      Complex.exp (-causalGap advanced μ a b*(t : ℂ))*(causalGap advanced μ a b)⁻¹ := by
  have he : (fun u : ℝ => Complex.exp (-causalGap advanced μ a b*((t+u : ℝ) : ℂ))) =
      fun u : ℝ => Complex.exp (-causalGap advanced μ a b*(t : ℂ))*Complex.exp (-causalGap advanced μ a b*(u : ℂ)) := by
    funext u
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact ⟨(decay_integrable advanced μ a b hμ).const_mul _, by rw [integral_const_mul, decay_integral advanced μ a b hμ]⟩
private theorem shifted_gram_integrable (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) (t : ℝ) :
    IntegrableOn (fun u : ℝ => timeGram advanced μ freq v (t+u)) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((shifted_decay_integral advanced μ (freq i) (freq j) t hμ).1).mul_const _))
private theorem shifted_gram_integral (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) (t : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)) =
      ∑ i, ∑ j, Complex.exp (-causalGap advanced μ (freq i) (freq j)*(t : ℂ))*
        (causalGap advanced μ (freq i) (freq j))⁻¹*coefficient v i j := by
  unfold timeGram
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((shifted_decay_integral advanced μ (freq i) (freq j) t hμ).1).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => ((shifted_decay_integral advanced μ (freq i) (freq j) t hμ).1).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, (shifted_decay_integral advanced μ (freq i) (freq j) t hμ).2]
private theorem double_gram_integral (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) :
    IntegrableOn (fun t : ℝ => ∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)) = doubleGram advanced μ freq v := by
  simp_rw [shifted_gram_integral advanced μ hμ freq v]
  have hi : IntegrableOn (fun t : ℝ => ∑ i, ∑ j, Complex.exp (-causalGap advanced μ (freq i) (freq j)*(t : ℂ))*
      (causalGap advanced μ (freq i) (freq j))⁻¹*coefficient v i j) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      ((decay_integrable advanced μ (freq i) (freq j) hμ).mul_const _).mul_const _))
  refine ⟨hi, ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((decay_integrable advanced μ (freq i) (freq j) hμ).mul_const _).mul_const _))]
  unfold doubleGram
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => ((decay_integrable advanced μ (freq i) (freq j) hμ).mul_const _).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, integral_mul_const, decay_integral advanced μ (freq i) (freq j) hμ, pow_two]

/-- The causal derivative Gram is paid by a double positive-time original source norm square.
Every ordered interference term is retained before positivity is applied. -/
theorem actual_radial_causal_double_gram_nonnegative (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (freq : ι → ℝ) (v : ι → QuantumTest) : 0 ≤ (doubleGram advanced μ freq v).re := by
  have hd := double_gram_integral advanced μ hμ freq v
  have hr : (∫ t : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)).re =
      ∫ t : ℝ in Set.Ioi 0, (∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)).re := by
    simpa only using! (integral_re hd.1).symm
  rw [← hd.2, hr]
  apply integral_nonneg
  intro t
  change 0 ≤ (∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)).re
  have hr' : (∫ u : ℝ in Set.Ioi 0, timeGram advanced μ freq v (t+u)).re =
      ∫ u : ℝ in Set.Ioi 0, (timeGram advanced μ freq v (t+u)).re := by
    simpa only using! (integral_re (shifted_gram_integrable advanced μ hμ freq v t)).symm
  rw [hr']
  apply integral_nonneg
  intro u
  change 0 ≤ (timeGram advanced μ freq v (t+u)).re
  rw [time_gram_value]
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

private theorem causal_triple_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => star (causalPole advanced μ a ω) ^ 2 * causalPole advanced μ b ω) := by
  cases advanced
  · simpa only [causalPole, Bool.false_eq_true, ite_false] using actual_scalar_causal_triple_integrable μ a b hμ
  · have h := (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (actual_scalar_causal_triple_integrable μ a b hμ)
    exact h.congr (Eventually.of_forall (fun ω => by
      change star (star (pole μ a ω) ^ 2 * pole μ b ω) =
        star (causalPole true μ a ω) ^ 2 * causalPole true μ b ω
      simp only [causalPole, ite_true, star_mul, star_pow, star_star]
      ring))
private theorem causal_triple_integral (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ ω : ℝ, star (causalPole advanced μ a ω) ^ 2 * causalPole advanced μ b ω) =
      ((-2*Real.pi*causalDirection advanced : ℝ) : ℂ)*Complex.I*(causalGap advanced μ a b)⁻¹ ^ 2 := by
  cases advanced
  · simpa [causalPole, causalGap, causalDirection, div_eq_mul_inv, inv_pow] using actual_scalar_causal_triple_integral μ a b hμ
  · have he : (∫ ω : ℝ, star (causalPole true μ a ω) ^ 2 * causalPole true μ b ω) =
        star (∫ ω : ℝ, star (pole μ a ω) ^ 2 * pole μ b ω) := by
      calc
        _ = ∫ ω : ℝ, star (star (pole μ a ω) ^ 2 * pole μ b ω) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun ω => by
            simp only [causalPole, ite_true, star_mul, star_pow, star_star]
            ring)
        _ = _ := integral_conj
    rw [actual_scalar_causal_triple_integral μ a b hμ] at he
    simpa [causalGap, causalDirection, Complex.star_def, div_eq_mul_inv, inv_pow] using he

private def frequencyGram (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (ω : ℝ) : ℂ :=
  ∑ i, ∑ j, (star (causalPole advanced μ (freq i) ω) ^ 2 * causalPole advanced μ (freq j) ω)*coefficient v i j
private theorem frequency_gram_value (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (ω : ℝ) :
    frequencyGram advanced μ freq v ω =
      sourcePair (scalarFrequencyDerivative advanced μ freq v ω)
        (scalarFrequencyWave advanced μ freq v ω) := by
  symm
  simp only [scalarFrequencyDerivative, scalarFrequencyWave, frequencyGram, coefficient,
    sourcePair, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem frequency_gram_integrable (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) :
    Integrable (frequencyGram advanced μ freq v) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (causal_triple_integrable advanced μ (freq i) (freq j) hμ).mul_const _))
private theorem frequency_gram_integral (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (freq : ι → ℝ) (v : ι → QuantumTest) :
    (∫ ω : ℝ, frequencyGram advanced μ freq v ω) =
      ((-2*Real.pi*causalDirection advanced : ℝ) : ℂ)*Complex.I*doubleGram advanced μ freq v := by
  unfold frequencyGram
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (causal_triple_integrable advanced μ (freq i) (freq j) hμ).mul_const _))]
  unfold doubleGram
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (causal_triple_integrable advanced μ (freq i) (freq j) hμ).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, causal_triple_integral advanced μ (freq i) (freq j) hμ]
  ring

/-- The virtual-frequency cross is nonpositive only after the actual ordered
causal profile is integrated. No commutation with the radial source columns is needed. -/
theorem actual_radial_causal_frequency_cross_payment (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (freq : ι → ℝ) (v : ι → QuantumTest) :
    Integrable (fun ω : ℝ => sourcePair (scalarFrequencyDerivative advanced μ freq v ω)
      (scalarFrequencyWave advanced μ freq v ω)) ∧
    (causalDirection advanced*μ)*(∫ ω : ℝ,
      (sourcePair (scalarFrequencyDerivative advanced μ freq v ω)
        (scalarFrequencyWave advanced μ freq v ω)).im) ≤ 0 := by
  have hi := frequency_gram_integrable advanced μ hμ freq v
  refine ⟨hi.congr (Eventually.of_forall (frequency_gram_value advanced μ freq v)), ?_⟩
  have him : (∫ ω : ℝ, (frequencyGram advanced μ freq v ω).im) =
      (∫ ω : ℝ, frequencyGram advanced μ freq v ω).im := by
    simpa only using! integral_im hi
  simp_rw [← frequency_gram_value]
  rw [him, frequency_gram_integral advanced μ hμ freq v]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, sub_zero, mul_one]
  have hp := actual_radial_causal_double_gram_nonnegative advanced μ hμ freq v
  have hn : 0 ≤ (2*Real.pi*μ)*(doubleGram advanced μ freq v).re :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hμ.le) hp
  cases advanced <;> simp only [causalDirection, Bool.false_eq_true, ite_false, ite_true, neg_one_mul, one_mul]
  all_goals nlinarith only [hn]

private theorem causal_pole_actual(advanced:Bool)(μ a q:ℝ):
    causalPole advanced μ a q=((a:ℂ)-SourceLocalizedInverseFormPayment.actualFrequency advanced μ q)⁻¹:=by
  cases advanced <;> simp [causalPole,pole,SourceLocalizedInverseFormPayment.actualFrequency]
private theorem fixed_wave(advanced:Bool)(μ:ℝ)(freq:ι→ℝ)(v:ι→QuantumTest)(q:ℝ):
    fixedSourceWave advanced μ freq v q=scalarFrequencyWave advanced μ freq v q:=by
  unfold fixedSourceWave scalarFrequencyWave
  simp_rw [causal_pole_actual]
private theorem fixed_derivative(advanced:Bool)(μ:ℝ)(freq:ι→ℝ)(v:ι→QuantumTest)(q:ℝ):
    fixedSourceDerivative advanced μ freq v q=scalarFrequencyDerivative advanced μ freq v q:=by
  unfold fixedSourceDerivative scalarFrequencyDerivative
  simp_rw [causal_pole_actual]
private theorem pair_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re:=by
  simpa only [Complex.conj_re] using congrArg Complex.re (GaussNativeForm.pair_conjugate f g)
private theorem point_frequency(z:ℂ)(u v:QuantumTest):
    (sourcePair (z • u) v).re=(sourcePair (z • v) u).re-2*z.im*(sourcePair v u).im:=by
  have h:=GaussNativeForm.pair_conjugate v u
  simp only [sourcePair,map_smul,inner_smul_left,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  unfold sourcePair at h
  rw [←h]
  simp only [Complex.conj_re,Complex.conj_im]
  ring

/-- The full frequency-dilation word loses at least half its norm mass. The ordered virtual-frequency contribution is paid by the causal source Gram, for both causes. -/
theorem actual_radial_frequency_dilation(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ι→ℝ)(v:ι→QuantumTest):
    Integrable (fun q:ℝ=>sourcePair (scalarFrequencyWave advanced μ freq v q)
      (scalarFrequencyWave advanced μ freq v q+SourceLocalizedInverseFormPayment.actualFrequency advanced μ q •
        scalarFrequencyDerivative advanced μ freq v q)) ∧
    (∫q:ℝ,(sourcePair (scalarFrequencyWave advanced μ freq v q)
      (scalarFrequencyWave advanced μ freq v q+SourceLocalizedInverseFormPayment.actualFrequency advanced μ q •
        scalarFrequencyDerivative advanced μ freq v q)).re)≤
      (1/2:ℝ)*(∫q:ℝ,‖embed (scalarFrequencyWave advanced μ freq v q)‖^2):=by
  let w:=scalarFrequencyWave advanced μ freq v
  let wp:=scalarFrequencyDerivative advanced μ freq v
  let z:=SourceLocalizedInverseFormPayment.actualFrequency advanced μ
  have h:=actual_fixed_source_frequency_pair advanced μ hμ freq v v
  simp_rw [fixed_wave,fixed_derivative] at h
  have hc:=actual_radial_causal_frequency_cross_payment advanced μ hμ freq v
  have hconj:Integrable (fun q:ℝ=>star (sourcePair (z q • wp q) (w q))):=
    (RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp h.2.1
  have he(q:ℝ):sourcePair (w q) (w q+z q • wp q)=sourcePair (w q) (w q)+star (sourcePair (z q • wp q) (w q)):=by
    have hp:star (sourcePair (z q • wp q) (w q))=sourcePair (w q) (z q • wp q):=by
      simpa only [starRingEnd_apply] using GaussNativeForm.pair_conjugate (z q • wp q) (w q)
    rw [hp]
    simp only [sourcePair,map_add,inner_add_right]
  have hi:Integrable (fun q:ℝ=>sourcePair (w q) (w q+z q • wp q)):=
    (h.1.add hconj).congr (Eventually.of_forall (fun q=>(he q).symm))
  refine ⟨hi,?_⟩
  have him(q:ℝ):(z q).im=causalDirection advanced*μ:=by
    cases advanced <;> simp [z,SourceLocalizedInverseFormPayment.actualFrequency,causalDirection,line_im]
  have hnr:Integrable (fun q:ℝ=>(sourcePair (w q) (w q)).re):=by
    simpa only [RCLike.re_eq_complex_re] using h.1.re
  have hcr:Integrable (fun q:ℝ=>(sourcePair (z q • wp q) (w q)).re):=by
    simpa only [RCLike.re_eq_complex_re] using h.2.1.re
  have hci:Integrable (fun q:ℝ=>(sourcePair (wp q) (w q)).im):=by
    simpa only [RCLike.im_eq_complex_im] using hc.1.im
  have hp:(∫q:ℝ,(sourcePair (z q • w q) (wp q)).re)=
      (∫q:ℝ,(sourcePair (z q • wp q) (w q)).re)-2*(causalDirection advanced*μ)*
        (∫q:ℝ,(sourcePair (wp q) (w q)).im):=by
    calc
      _=∫q:ℝ,(sourcePair (z q • wp q) (w q)).re-2*(causalDirection advanced*μ)*(sourcePair (wp q) (w q)).im:=by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q=>by dsimp only;rw [point_frequency,him])
      _=_:=by
        rw [integral_sub hcr (hci.const_mul _),integral_const_mul]
  have hb:=congrArg Complex.re h.2.2.2
  simp only [Complex.neg_re,Complex.sub_re] at hb
  have hr {f:ℝ→ℂ}(hf:Integrable f):(∫q:ℝ,f q).re=∫q:ℝ,(f q).re:=by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hf).symm
  rw [hr h.1,hr h.2.1,hr h.2.2.1] at hb
  have hn(q:ℝ):(sourcePair (w q) (w q)).re=‖embed (w q)‖^2:=by
    simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed (w q))
  change (∫q:ℝ,(sourcePair (w q) (w q+z q • wp q)).re)≤_
  simp_rw [he,Complex.add_re,Complex.star_def,Complex.conj_re]
  rw [integral_add hnr hcr]
  change (∫q:ℝ,(sourcePair (z q • wp q) (w q)).re)=
    -(∫q:ℝ,(sourcePair (w q) (w q)).re)-(∫q:ℝ,(sourcePair (z q • w q) (wp q)).re) at hb
  simp_rw [hn] at hb
  simp_rw [hn]
  change (∫q:ℝ,‖embed (w q)‖^2)+(∫q:ℝ,(sourcePair (z q • wp q) (w q)).re)≤
    (1/2:ℝ)*(∫q:ℝ,‖embed (w q)‖^2)
  have hsign:(causalDirection advanced*μ)*(∫q:ℝ,(sourcePair (wp q) (w q)).im)≤0:=hc.2
  linarith only [hb,hp,hsign]
end LowEnergy.FirstCurrentRadialDifferenceDissipation
