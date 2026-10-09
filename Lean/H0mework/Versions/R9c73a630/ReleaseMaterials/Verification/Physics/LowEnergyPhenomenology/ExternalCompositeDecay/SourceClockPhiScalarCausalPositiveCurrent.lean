import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarCausalFrequencyKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarCausalFrequencyMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarInverseNativeEnergy
open SourceScalarDoubleCurrent SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
variable {ι : Type*} [Fintype ι]
attribute [local irreducible] sourcePair embed scalarBulkComplete scalarEnergy inverseNativeEnergy shiftedMoment

def causalPole (advanced : Bool) (μ a ω : ℝ) : ℂ :=
  if advanced then star (pole μ a ω) else pole μ a ω
def causalGap (advanced : Bool) (μ a b : ℝ) : ℂ :=
  if advanced then star (gap μ a b) else gap μ a b
def causalDirection (advanced : Bool) : ℝ := if advanced then -1 else 1
def scalarCausalWave (advanced : Bool) (freq : ι → ℝ) (v : ι → QuantumTest) (t : ℝ) : QuantumTest :=
  ∑ i, Complex.exp (-((causalDirection advanced : ℝ) : ℂ)*Complex.I*(freq i : ℂ)*(t : ℂ)) • v i
def scalarFrequencyWave (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (ω : ℝ) : QuantumTest :=
  ∑ i, causalPole advanced μ (freq i) ω • v i
def scalarFrequencyDerivative (advanced : Bool) (μ : ℝ) (freq : ι → ℝ) (v : ι → QuantumTest) (ω : ℝ) : QuantumTest :=
  ∑ i, causalPole advanced μ (freq i) ω ^ 2 • v i
private def coefficient (v : ι → QuantumTest) (i j : ι) : ℂ := sourcePair (v i) (scalarBulkComplete (v j))
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
    (timeGram advanced μ freq v t).re = Real.exp (-2*μ*t)*scalarEnergy (scalarCausalWave advanced freq v t) := by
  have hs : sourcePair (scalarCausalWave advanced freq v t) (scalarBulkComplete (scalarCausalWave advanced freq v t)) =
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
      sourcePair (scalarCausalWave advanced freq v t) (scalarBulkComplete (scalarCausalWave advanced freq v t)) := by
    unfold timeGram
    simp_rw [time_factor]
    rw [hs]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ht, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, original_scalar_energy]
private theorem scalar_nonnegative (w : QuantumTest) : 0 ≤ scalarEnergy w := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hI : 0 ≤ inverseNativeEnergy w := by
    unfold inverseNativeEnergy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : 0 ≤ shiftedMoment w := by
    unfold shiftedMoment
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold scalarEnergy
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn.le) hI)
    (mul_nonneg (mul_nonneg (by norm_num) hn.le) hS)

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

/-- The causal derivative Gram is paid by a double positive-time scalar form.
Every ordered interference term is retained before positivity is applied. -/
theorem actual_scalar_causal_double_gram_nonnegative (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
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
  exact mul_nonneg (Real.exp_pos _).le (scalar_nonnegative _)

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
        (scalarBulkComplete (scalarFrequencyWave advanced μ freq v ω)) := by
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
causal profile is integrated. No commutation with the scalar form is needed. -/
theorem actual_scalar_causal_frequency_cross_payment (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (freq : ι → ℝ) (v : ι → QuantumTest) :
    Integrable (fun ω : ℝ => sourcePair (scalarFrequencyDerivative advanced μ freq v ω)
      (scalarBulkComplete (scalarFrequencyWave advanced μ freq v ω))) ∧
    (causalDirection advanced*μ)*(∫ ω : ℝ,
      (sourcePair (scalarFrequencyDerivative advanced μ freq v ω)
        (scalarBulkComplete (scalarFrequencyWave advanced μ freq v ω))).im) ≤ 0 := by
  have hi := frequency_gram_integrable advanced μ hμ freq v
  refine ⟨hi.congr (Eventually.of_forall (frequency_gram_value advanced μ freq v)), ?_⟩
  have him : (∫ ω : ℝ, (frequencyGram advanced μ freq v ω).im) =
      (∫ ω : ℝ, frequencyGram advanced μ freq v ω).im := by
    simpa only using! integral_im hi
  simp_rw [← frequency_gram_value]
  rw [him, frequency_gram_integral advanced μ hμ freq v]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, sub_zero, mul_one]
  have hp := actual_scalar_causal_double_gram_nonnegative advanced μ hμ freq v
  have hn : 0 ≤ (2*Real.pi*μ)*(doubleGram advanced μ freq v).re :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hμ.le) hp
  cases advanced <;> simp only [causalDirection, Bool.false_eq_true, ite_false, ite_true, neg_one_mul, one_mul]
  all_goals nlinarith only [hn]
end LowEnergy.ScalarCausalFrequencyMoment
