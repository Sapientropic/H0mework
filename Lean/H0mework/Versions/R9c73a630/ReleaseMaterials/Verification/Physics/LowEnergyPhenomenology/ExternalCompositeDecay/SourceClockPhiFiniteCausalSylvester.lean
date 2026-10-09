import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace LowEnergy.FiniteCausalSylvester

def causalSign (advanced : Bool) : ℝ := if advanced then -1 else 1

def causalGap (advanced : Bool) (μ a b : ℝ) : ℂ :=
  2 * (μ : ℂ) + Complex.I * ((causalSign advanced * (b-a) : ℝ) : ℂ)

def causalGram (advanced : Bool) (μ a b : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) / causalGap advanced μ a b

private theorem causalGap_ne (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    causalGap advanced μ a b ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [causalGap] at hr
  linarith

/-- The source clock gap is removed before any absolute-value estimate. -/
theorem causalGram_clock_difference (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    causalGram advanced μ a b * ((b-a : ℝ) : ℂ) =
      (2 * Complex.I * ((causalSign advanced * μ : ℝ) : ℂ)) *
        causalGram advanced μ a b -
      2 * (Real.pi : ℂ) * Complex.I * (causalSign advanced : ℂ) := by
  have hn := causalGap_ne advanced μ a b hμ
  unfold causalGram
  apply (eq_sub_iff_add_eq).mpr
  apply (mul_left_cancel₀ hn)
  field_simp [hn]
  cases advanced <;> simp [causalGap, causalSign] <;>
    ring_nf <;> simp [Complex.I_sq]

variable {ι : Type*} [Fintype ι]

def gramRead (advanced : Bool) (μ : ℝ) (eig : ι → ℝ) (B : ι → ι → ℂ) : ℂ :=
  ∑ i, ∑ j, causalGram advanced μ (eig i) (eig j) * B i j

/-- The only endpoint is the total source column; its generated zero value removes it exactly. -/
theorem zero_column_sylvester (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (eig : ι → ℝ) (B : ι → ι → ℂ) (hB : (∑ i, ∑ j, B i j) = 0) :
    gramRead advanced μ eig (fun i j => ((eig j - eig i : ℝ) : ℂ) * B i j) =
      (2 * Complex.I * ((causalSign advanced * μ : ℝ) : ℂ)) * gramRead advanced μ eig B := by
  unfold gramRead
  have hp (i j : ι) :
      causalGram advanced μ (eig i) (eig j) * (((eig j - eig i : ℝ) : ℂ) * B i j) =
        (2 * Complex.I * ((causalSign advanced * μ : ℝ) : ℂ)) *
          (causalGram advanced μ (eig i) (eig j) * B i j) -
        (2 * (Real.pi : ℂ) * Complex.I * (causalSign advanced : ℂ)) * B i j := by
    rw [←mul_assoc, causalGram_clock_difference advanced μ (eig i) (eig j) hμ]
    ring
  simp_rw [hp, Finset.sum_sub_distrib, ←Finset.mul_sum]
  rw [hB, mul_zero, sub_zero]

/-- A whole skew clock commutator and its physical phase consume the same Sylvester identity. -/
theorem clock_phase_cancellation (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (eig : ι → ℝ) (B D : ι → ι → ℂ) (hB : (∑ i, ∑ j, B i j) = 0) :
    3 * (gramRead advanced μ eig
      (fun i j => D i j - ((eig j - eig i : ℝ) : ℂ) * B i j)).re -
      6 * (causalSign advanced * μ) * (gramRead advanced μ eig B).im =
        3 * (gramRead advanced μ eig D).re := by
  have hs := zero_column_sylvester advanced μ hμ eig B hB
  have he : gramRead advanced μ eig
      (fun i j => D i j - ((eig j - eig i : ℝ) : ℂ) * B i j) =
      gramRead advanced μ eig D -
        (2 * Complex.I * ((causalSign advanced * μ : ℝ) : ℂ)) * gramRead advanced μ eig B := by
    rw [←hs]
    simp only [gramRead, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.I_re, Complex.I_im]
  ring

/-- Exact payment of the full signed Noether cross term by its existing clock square. -/
theorem noether_clock_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℝ) (hn : 0 < n) (b d : E) :
    -6 * (inner ℂ b d).re - (n/48) * ‖b‖^2 =
      (432/n) * ‖d‖^2 - (n/48) * ‖b + ((144/n : ℝ) : ℂ) • d‖^2 := by
  have hc : 0 ≤ 144/n := by positivity
  have hs := norm_add_sq (𝕜 := ℂ) b (((144/n : ℝ) : ℂ) • d)
  simp only [inner_smul_right, RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc] at hs
  rw [hs]
  field_simp [hn.ne']
  ring

theorem noether_clock_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℝ) (hn : 0 < n) (b d : E) :
    -6 * (inner ℂ b d).re - (n/48) * ‖b‖^2 ≤ (432/n) * ‖d‖^2 := by
  rw [noether_clock_square n hn]
  exact sub_le_self _ (mul_nonneg (by positivity) (sq_nonneg _))


open MeasureTheory
open scoped InnerProductSpace

private def abelEntry (advanced : Bool) (μ a b t : ℝ) : ℂ :=
  Complex.exp (-causalGap advanced μ a b * (t : ℂ))

private theorem abelEntry_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    IntegrableOn (abelEntry advanced μ a b) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp only [causalGap, Complex.neg_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.I_re, Complex.I_im]
  linarith

private theorem abelEntry_integral (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ t : ℝ in Set.Ioi 0, abelEntry advanced μ a b t) =
      (causalGap advanced μ a b)⁻¹ := by
  have hneg : (-causalGap advanced μ a b).re < 0 := by
    simp only [causalGap, Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.I_re, Complex.I_im]
    linarith
  unfold abelEntry
  rw [integral_exp_mul_complex_Ioi hneg 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div,
    neg_neg, one_div]

private def abelWord (advanced : Bool) (μ : ℝ) (eig : ι → ℝ)
    (B : ι → ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, abelEntry advanced μ (eig i) (eig j) t * B i j

private theorem abelWord_integrable (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (eig : ι → ℝ) (B : ι → ι → ℂ) :
    IntegrableOn (abelWord advanced μ eig B) (Set.Ioi 0) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (abelEntry_integrable advanced μ (eig i) (eig j) hμ).mul_const _

private theorem gramRead_integral (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (eig : ι → ℝ) (B : ι → ι → ℂ) :
    gramRead advanced μ eig B =
      2 * (Real.pi : ℂ) * (∫ t : ℝ in Set.Ioi 0, abelWord advanced μ eig B t) := by
  unfold gramRead abelWord
  have hr (i : ι) : IntegrableOn (fun t : ℝ =>
      ∑ j, abelEntry advanced μ (eig i) (eig j) t * B i j) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun j _ =>
      (abelEntry_integrable advanced μ (eig i) (eig j) hμ).mul_const _)
  rw [integral_finsetSum _ (fun i _ => hr i)]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (abelEntry_integrable advanced μ _ (eig j) hμ).mul_const _)]
  simp only [integral_mul_const, abelEntry_integral advanced μ _ _ hμ,
    Finset.mul_sum, causalGram, div_eq_mul_inv, mul_assoc]

private theorem abelWord_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (advanced : Bool) (μ : ℝ) (eig : ι → ℝ) (v : ι → E) (t : ℝ) :
    (abelWord advanced μ eig (fun i j => inner ℂ (v i) (v j)) t).re =
      Real.exp (-2 * μ * t) *
        ‖∑ i, Complex.exp (-Complex.I * ((causalSign advanced * eig i : ℝ) : ℂ) * (t : ℂ)) • v i‖^2 := by
  let q := fun i => Complex.exp (-Complex.I * ((causalSign advanced * eig i : ℝ) : ℂ) * (t : ℂ))
  have hc (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.star_exp z
  have he (i j : ι) : abelEntry advanced μ (eig i) (eig j) t =
      (Real.exp (-2 * μ * t) : ℂ) * star (q i) * q j := by
    unfold abelEntry q
    rw [hc, Complex.ofReal_exp, ←Complex.exp_add, ←Complex.exp_add]
    congr 1
    simp only [causalGap, star_mul, star_neg, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_sub]
    ring
  have hsum : abelWord advanced μ eig (fun i j => inner ℂ (v i) (v j)) t =
      (Real.exp (-2 * μ * t) : ℂ) * inner ℂ (∑ i, q i • v i) (∑ j, q j • v j) := by
    unfold abelWord
    simp only [he, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : (inner ℂ (∑ i, q i • v i) (∑ i, q i • v i)).re = ‖∑ i, q i • v i‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (∑ i, q i • v i)).symm
  rw [hsum, Complex.mul_re, hn]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Positivity comes from the actual causal clock Gram, including all off-diagonal columns. -/
theorem causalGram_nonnegative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (eig : ι → ℝ) (v : ι → E) :
    0 ≤ (gramRead advanced μ eig (fun i j => inner ℂ (v i) (v j))).re := by
  have hi := abelWord_integrable advanced μ hμ eig (fun i j => inner ℂ (v i) (v j))
  have hr : (∫ t : ℝ in Set.Ioi 0, abelWord advanced μ eig
      (fun i j => inner ℂ (v i) (v j)) t).re =
      ∫ t : ℝ in Set.Ioi 0, (abelWord advanced μ eig
        (fun i j => inner ℂ (v i) (v j)) t).re :=
    (Complex.reCLM.integral_comp_comm hi).symm
  rw [gramRead_integral advanced μ hμ, Complex.mul_re, Complex.mul_re,
    Complex.mul_im, hr]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro t
  change 0 ≤ (abelWord advanced μ eig (fun i j => inner ℂ (v i) (v j)) t).re
  rw [abelWord_pair]
  positivity


private theorem gramRead_add (advanced : Bool) (μ : ℝ) (eig : ι → ℝ)
    (B D : ι → ι → ℂ) :
    gramRead advanced μ eig (fun i j => B i j + D i j) =
      gramRead advanced μ eig B + gramRead advanced μ eig D := by
  simp only [gramRead, mul_add, Finset.sum_add_distrib]

private theorem gramRead_scale (advanced : Bool) (μ : ℝ) (eig : ι → ℝ)
    (c : ℂ) (B : ι → ι → ℂ) :
    gramRead advanced μ eig (fun i j => c * B i j) = c * gramRead advanced μ eig B := by
  unfold gramRead
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem gramRead_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (advanced : Bool) (μ : ℝ) (eig : ι → ℝ) (b d : ι → E) (c : ℝ) :
    (gramRead advanced μ eig (fun i j => inner ℂ (b i + (c : ℂ) • d i)
      (b j + (c : ℂ) • d j))).re =
      (gramRead advanced μ eig (fun i j => inner ℂ (b i) (b j))).re +
      c * (gramRead advanced μ eig (fun i j =>
        inner ℂ (b i) (d j) + inner ℂ (d i) (b j))).re +
      c^2 * (gramRead advanced μ eig (fun i j => inner ℂ (d i) (d j))).re := by
  have he (i j : ι) : inner ℂ (b i + (c : ℂ) • d i) (b j + (c : ℂ) • d j) =
      inner ℂ (b i) (b j) + (c : ℂ) * (inner ℂ (b i) (d j) + inner ℂ (d i) (b j)) +
      ((c^2 : ℝ) : ℂ) * inner ℂ (d i) (d j) := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  simp_rw [he]
  rw [gramRead_add, gramRead_add, gramRead_scale, gramRead_scale]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- No loss of off-diagonal signs: the complete clock square pays both physical source legs
inside the same causal Gram, without a frequency or Gaussian norm bound as a premise. -/
theorem causalGram_noether_payment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (eig : ι → ℝ) (b d : ι → E)
    (n : ℝ) (hn : 0 < n) :
    -3 * (gramRead advanced μ eig (fun i j =>
      inner ℂ (b i) (d j) + inner ℂ (d i) (b j))).re -
      (n/48) * (gramRead advanced μ eig (fun i j => inner ℂ (b i) (b j))).re ≤
      (432/n) * (gramRead advanced μ eig (fun i j => inner ℂ (d i) (d j))).re := by
  have hp := causalGram_nonnegative advanced μ hμ eig (fun i => b i + ((144/n : ℝ) : ℂ) • d i)
  rw [gramRead_square] at hp
  have hn0 : n ≠ 0 := hn.ne'
  have hmul := mul_nonneg (show 0 ≤ n/48 by positivity) hp
  have he : (n/48) * ((gramRead advanced μ eig (fun i j => inner ℂ (b i) (b j))).re +
      (144/n) * (gramRead advanced μ eig (fun i j =>
        inner ℂ (b i) (d j) + inner ℂ (d i) (b j))).re +
      (144/n)^2 * (gramRead advanced μ eig (fun i j => inner ℂ (d i) (d j))).re) =
      (n/48) * (gramRead advanced μ eig (fun i j => inner ℂ (b i) (b j))).re +
      3 * (gramRead advanced μ eig (fun i j =>
        inner ℂ (b i) (d j) + inner ℂ (d i) (b j))).re +
      (432/n) * (gramRead advanced μ eig (fun i j => inner ℂ (d i) (d j))).re := by
    field_simp [hn0]
    ring
  rw [he] at hmul
  linarith only [hmul]


private theorem causalGram_star (advanced : Bool) (μ a b : ℝ) :
    star (causalGram advanced μ a b) = causalGram advanced μ b a := by
  have hg : star (causalGap advanced μ a b) = causalGap advanced μ b a := by
    simp only [causalGap, star_add, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_ofNat, Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_sub, map_sub]
    ring
  unfold causalGram
  rw [star_div₀, star_mul, hg]
  simp only [Complex.star_def, Complex.conj_ofNat, Complex.conj_ofReal]
  ring

/-- A paired source form retains its real value in the entire two-cause clock Gram. -/
theorem paired_gram_real (advanced : Bool) (μ : ℝ) (eig : ι → ℝ)
    (B : ι → ι → ℂ) (hB : ∀ i j, star (B i j) = B j i) :
    (gramRead advanced μ eig B).im = 0 := by
  have he : star (gramRead advanced μ eig B) = gramRead advanced μ eig B := by
    unfold gramRead
    simp only [star_sum, star_mul, causalGram_star, hB]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end LowEnergy.FiniteCausalSylvester
