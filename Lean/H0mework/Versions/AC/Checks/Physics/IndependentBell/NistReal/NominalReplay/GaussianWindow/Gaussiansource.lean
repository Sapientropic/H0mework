import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
The two raw geometric ratios and a unit-circle phase generate every paired number
amplitude. Normalization, the count PGF and factorial moments are consequences of
geometric series. A number-conserving effect is compressed to the actual paired
support in each total-number sector; its positivity and contraction are effect
legality, rather than a supplied source, probability or covariance certificate.
-/

set_option autoImplicit false

namespace P23.GaussianWindow

open scoped BigOperators ComplexOrder
open Matrix
noncomputable section

structure RawKernel where
  tH : ℝ
  tV : ℝ
  phase : ℂ
  tH_nonneg : 0 ≤ tH
  tH_lt_one : tH < 1
  tV_nonneg : 0 ≤ tV
  tV_lt_one : tV < 1
  phase_unit : Complex.normSq phase = 1

def geometricMass (t : ℝ) (n : ℕ) : ℝ := (1 - t) * t ^ n

theorem geometricMass_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (n : ℕ) :
    0 ≤ geometricMass t n :=
  mul_nonneg (sub_nonneg.mpr h1.le) (pow_nonneg h0 n)

theorem geometricMass_hasSum {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (geometricMass t) 1 := by
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr h1)
  convert! (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - t) using 1
  simp [hden]

def numberMass (s : RawKernel) (h v : ℕ) : ℝ :=
  geometricMass s.tH h * geometricMass s.tV v

theorem numberMass_nonneg (s : RawKernel) (h v : ℕ) : 0 ≤ numberMass s h v :=
  mul_nonneg (geometricMass_nonneg s.tH_nonneg s.tH_lt_one h)
    (geometricMass_nonneg s.tV_nonneg s.tV_lt_one v)

theorem numberMass_raw (s : RawKernel) (h v : ℕ) :
    numberMass s h v = (1 - s.tH) * (1 - s.tV) * s.tH ^ h * s.tV ^ v := by
  dsimp [numberMass, geometricMass]
  ring

theorem numberMass_summable (s : RawKernel) :
    Summable (fun hv : ℕ × ℕ => numberMass s hv.1 hv.2) :=
  (geometricMass_hasSum s.tH_nonneg s.tH_lt_one).summable.mul_of_nonneg
    (geometricMass_hasSum s.tV_nonneg s.tV_lt_one).summable
    (fun h => geometricMass_nonneg s.tH_nonneg s.tH_lt_one h)
    (fun v => geometricMass_nonneg s.tV_nonneg s.tV_lt_one v)

theorem numberMass_hasSum (s : RawKernel) :
    HasSum (fun hv : ℕ × ℕ => numberMass s hv.1 hv.2) 1 := by
  simpa only [numberMass, one_mul] using
    (geometricMass_hasSum s.tH_nonneg s.tH_lt_one).mul
      (geometricMass_hasSum s.tV_nonneg s.tV_lt_one) (numberMass_summable s)

def amplitude (s : RawKernel) (h v : ℕ) : ℂ :=
  (Real.sqrt (1 - s.tH) : ℂ) * (Real.sqrt (1 - s.tV) : ℂ) *
    (Real.sqrt s.tH : ℂ) ^ h * (Real.sqrt s.tV : ℂ) ^ v * s.phase ^ v

theorem amplitude_normSq (s : RawKernel) (h v : ℕ) :
    Complex.normSq (amplitude s h v) = numberMass s h v := by
  simp only [amplitude, map_mul, map_pow, Complex.normSq_ofReal,
    Real.mul_self_sqrt (sub_nonneg.mpr s.tH_lt_one.le),
    Real.mul_self_sqrt (sub_nonneg.mpr s.tV_lt_one.le),
    Real.mul_self_sqrt s.tH_nonneg, Real.mul_self_sqrt s.tV_nonneg,
    s.phase_unit, one_pow, mul_one]
  exact (numberMass_raw s h v).symm

theorem amplitude_normalized (s : RawKernel) :
    (∑' hv : ℕ × ℕ, Complex.normSq (amplitude s hv.1 hv.2)) = 1 := by
  simp only [amplitude_normSq]
  exact (numberMass_hasSum s).tsum_eq

def pairedAmplitude (s : RawKernel) (a b : ℕ × ℕ) : ℂ :=
  if a = b then amplitude s a.1 a.2 else 0

theorem pairedAmplitude_diagonal (s : RawKernel) (a : ℕ × ℕ) :
    pairedAmplitude s a a = amplitude s a.1 a.2 := by
  simp [pairedAmplitude]

theorem pairedAmplitude_off_pair (s : RawKernel) (a b : ℕ × ℕ) (hne : a ≠ b) :
    pairedAmplitude s a b = 0 := by
  simp only [pairedAmplitude, if_neg hne]

def countPGF (s : RawKernel) (zH zV : ℝ) : ℝ :=
  ∑' hv : ℕ × ℕ, numberMass s hv.1 hv.2 * zH ^ hv.1 * zV ^ hv.2

theorem geometricMass_weighted_hasSum {t z : ℝ} (ht0 : 0 ≤ t) (hz0 : 0 ≤ z)
    (htz : t * z < 1) :
    HasSum (fun n : ℕ => geometricMass t n * z ^ n) ((1 - t) / (1 - t * z)) := by
  simpa only [geometricMass, mul_pow, mul_assoc, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one (mul_nonneg ht0 hz0) htz).mul_left (1 - t)

theorem countPGF_hasSum (s : RawKernel) {zH zV : ℝ}
    (hH0 : 0 ≤ zH) (hV0 : 0 ≤ zV) (hH1 : s.tH * zH < 1)
    (hV1 : s.tV * zV < 1) :
    HasSum (fun hv : ℕ × ℕ => numberMass s hv.1 hv.2 * zH ^ hv.1 * zV ^ hv.2)
      (((1 - s.tH) / (1 - s.tH * zH)) * ((1 - s.tV) / (1 - s.tV * zV))) := by
  have hH := geometricMass_weighted_hasSum s.tH_nonneg hH0 hH1
  have hV := geometricMass_weighted_hasSum s.tV_nonneg hV0 hV1
  have hprod := hH.mul hV (hH.summable.mul_of_nonneg hV.summable
    (fun h => mul_nonneg (geometricMass_nonneg s.tH_nonneg s.tH_lt_one h)
      (pow_nonneg hH0 h))
    (fun v => mul_nonneg (geometricMass_nonneg s.tV_nonneg s.tV_lt_one v)
      (pow_nonneg hV0 v)))
  convert! hprod using 1
  ext hv
  dsimp [numberMass]
  ring

theorem countPGF_eq (s : RawKernel) {zH zV : ℝ}
    (hH0 : 0 ≤ zH) (hV0 : 0 ≤ zV) (hH1 : s.tH * zH < 1)
    (hV1 : s.tV * zV < 1) :
    countPGF s zH zV =
      ((1 - s.tH) / (1 - s.tH * zH)) * ((1 - s.tV) / (1 - s.tV * zV)) :=
  (countPGF_hasSum s hH0 hV0 hH1 hV1).tsum_eq

def meanNumber (t : ℝ) : ℝ := t / (1 - t)

def factorialMoment (t : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (n.descFactorial k : ℝ) * geometricMass t n

theorem factorialMoment_hasSum {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (k : ℕ) :
    HasSum (fun n : ℕ => (n.descFactorial k : ℝ) * geometricMass t n)
      ((k.factorial : ℝ) * meanNumber t ^ k) := by
  have hnorm : ‖t‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr h1)
  have hshift :
      HasSum (fun n : ℕ => ((n + k).descFactorial k : ℝ) * geometricMass t (n + k))
        ((k.factorial : ℝ) * meanNumber t ^ k) := by
    have hvalue :
        (k.factorial : ℝ) * (1 - t) * t ^ k * (1 / (1 - t) ^ (k + 1)) =
          (k.factorial : ℝ) * meanNumber t ^ k := by
      dsimp [meanNumber]
      rw [div_pow, pow_succ]
      field_simp [hden]
    have hbase := (hasSum_choose_mul_geometric_of_norm_lt_one k hnorm).mul_left
      ((k.factorial : ℝ) * (1 - t) * t ^ k)
    rw [hvalue] at hbase
    apply hbase.congr_fun
    intro n
    simp only [geometricMass, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul, pow_add]
    ring
  have hprefix :
      (∑ n ∈ Finset.range k, (n.descFactorial k : ℝ) * geometricMass t n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Nat.descFactorial_of_lt (Finset.mem_range.mp hn), Nat.cast_zero, zero_mul]
  simpa only [hprefix, add_zero] using
    (hasSum_nat_add_iff k
      (f := fun n : ℕ => (n.descFactorial k : ℝ) * geometricMass t n)
      (g := (k.factorial : ℝ) * meanNumber t ^ k)).mp hshift

theorem factorialMoment_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (k : ℕ) :
    factorialMoment t k = (k.factorial : ℝ) * meanNumber t ^ k :=
  (factorialMoment_hasSum h0 h1 k).tsum_eq

def mixedFactorialMoment (s : RawKernel) (k l : ℕ) : ℝ :=
  ∑' hv : ℕ × ℕ,
    (hv.1.descFactorial k : ℝ) * (hv.2.descFactorial l : ℝ) * numberMass s hv.1 hv.2

theorem mixedFactorialMoment_hasSum (s : RawKernel) (k l : ℕ) :
    HasSum (fun hv : ℕ × ℕ =>
      (hv.1.descFactorial k : ℝ) * (hv.2.descFactorial l : ℝ) * numberMass s hv.1 hv.2)
      (((k.factorial : ℝ) * meanNumber s.tH ^ k) *
        ((l.factorial : ℝ) * meanNumber s.tV ^ l)) := by
  have hH := factorialMoment_hasSum s.tH_nonneg s.tH_lt_one k
  have hV := factorialMoment_hasSum s.tV_nonneg s.tV_lt_one l
  have hprod := hH.mul hV (hH.summable.mul_of_nonneg hV.summable
    (fun h => mul_nonneg (Nat.cast_nonneg _) (geometricMass_nonneg s.tH_nonneg s.tH_lt_one h))
    (fun v => mul_nonneg (Nat.cast_nonneg _) (geometricMass_nonneg s.tV_nonneg s.tV_lt_one v)))
  convert! hprod using 1
  ext hv
  dsimp [numberMass]
  ring

theorem mixedFactorialMoment_eq (s : RawKernel) (k l : ℕ) :
    mixedFactorialMoment s k l =
      ((k.factorial : ℝ) * meanNumber s.tH ^ k) *
        ((l.factorial : ℝ) * meanNumber s.tV ^ l) :=
  (mixedFactorialMoment_hasSum s k l).tsum_eq

def sectorMass (s : RawKernel) (n : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (n + 1), numberMass s h (n - h)

theorem sectorMass_nonneg (s : RawKernel) (n : ℕ) : 0 ≤ sectorMass s n :=
  Finset.sum_nonneg fun h _ => numberMass_nonneg s h (n - h)

theorem sectorMass_summable (s : RawKernel) : Summable (sectorMass s) :=
  summable_sum_mul_range_of_summable_mul (numberMass_summable s)

theorem sectorMass_tsum (s : RawKernel) : (∑' n : ℕ, sectorMass s n) = 1 := by
  change (∑' n : ℕ, ∑ h ∈ Finset.range (n + 1),
    geometricMass s.tH h * geometricMass s.tV (n - h)) = 1
  have hprod := Summable.tsum_mul_tsum_eq_tsum_sum_range
    (geometricMass_hasSum s.tH_nonneg s.tH_lt_one).summable
    (geometricMass_hasSum s.tV_nonneg s.tV_lt_one).summable
    (numberMass_summable s)
  rw [← hprod]
  simp only [(geometricMass_hasSum s.tH_nonneg s.tH_lt_one).tsum_eq,
    (geometricMass_hasSum s.tV_nonneg s.tV_lt_one).tsum_eq, one_mul]

def sourcePrefix (s : RawKernel) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (cutoff + 1), sectorMass s n

def sourceTail (s : RawKernel) (cutoff : ℕ) : ℝ :=
  ∑' n : ℕ, sectorMass s (n + (cutoff + 1))

theorem sourcePrefix_add_tail (s : RawKernel) (cutoff : ℕ) :
    sourcePrefix s cutoff + sourceTail s cutoff = 1 := by
  simpa only [sourcePrefix, sourceTail, sectorMass_tsum s] using
    (sectorMass_summable s).sum_add_tsum_nat_add (cutoff + 1)

theorem sourceTail_eq (s : RawKernel) (cutoff : ℕ) :
    sourceTail s cutoff = 1 - sourcePrefix s cutoff := by
  linarith [sourcePrefix_add_tail s cutoff]

theorem sourceTail_raw (s : RawKernel) (cutoff : ℕ) :
    sourceTail s cutoff = 1 - (1 - s.tH) * (1 - s.tV) *
      ∑ n ∈ Finset.range (cutoff + 1),
        ∑ h ∈ Finset.range (n + 1), s.tH ^ h * s.tV ^ (n - h) := by
  rw [sourceTail_eq]
  congr 1
  simp only [sourcePrefix, sectorMass, numberMass_raw]
  simp only [Finset.mul_sum, mul_assoc]

theorem sourceTail_bounds (s : RawKernel) (cutoff : ℕ) :
    0 ≤ sourceTail s cutoff ∧ sourceTail s cutoff ≤ 1 := by
  have htail : 0 ≤ sourceTail s cutoff :=
    tsum_nonneg fun n => sectorMass_nonneg s (n + (cutoff + 1))
  have hprefix : 0 ≤ sourcePrefix s cutoff :=
    Finset.sum_nonneg fun n _ => sectorMass_nonneg s n
  exact ⟨htail, by linarith [sourcePrefix_add_tail s cutoff]⟩

def sectorVector (s : RawKernel) (n : ℕ) : Fin (n + 1) → ℂ :=
  fun h => amplitude s h.val (n - h.val)

theorem sectorVector_normSq (s : RawKernel) (n : ℕ) :
    (∑ h : Fin (n + 1), Complex.normSq (sectorVector s n h)) = sectorMass s n := by
  simp only [sectorVector, amplitude_normSq, sectorMass]
  exact Fin.sum_univ_eq_sum_range (fun h => numberMass s h (n - h)) (n + 1)

theorem sectorVector_mass (s : RawKernel) (n : ℕ) :
    star (sectorVector s n) ⬝ᵥ sectorVector s n = (sectorMass s n : ℂ) := by
  calc
    star (sectorVector s n) ⬝ᵥ sectorVector s n =
        ∑ h : Fin (n + 1), (Complex.normSq (sectorVector s n h) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def,
        Complex.normSq_eq_conj_mul_self]
    _ = (((∑ h : Fin (n + 1), Complex.normSq (sectorVector s n h)) : ℝ) : ℂ) := by
      norm_cast
    _ = (sectorMass s n : ℂ) := by rw [sectorVector_normSq]

structure NumberConservingEffect where
  block : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  positive : ∀ n, (block n).PosSemidef
  complement_positive : ∀ n, (1 - block n).PosSemidef

def sectorBorn (s : RawKernel) (e : NumberConservingEffect) (n : ℕ) : ℝ :=
  (star (sectorVector s n) ⬝ᵥ (e.block n *ᵥ sectorVector s n)).re

theorem sectorBorn_bounds (s : RawKernel) (e : NumberConservingEffect) (n : ℕ) :
    0 ≤ sectorBorn s e n ∧ sectorBorn s e n ≤ sectorMass s n := by
  have h0 := (Complex.nonneg_iff.mp
    ((e.positive n).dotProduct_mulVec_nonneg (sectorVector s n))).1
  have h1 := (Complex.nonneg_iff.mp
    ((e.complement_positive n).dotProduct_mulVec_nonneg (sectorVector s n))).1
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    sectorVector_mass, Complex.sub_re, Complex.ofReal_re] at h1
  change 0 ≤ sectorBorn s e n at h0
  change 0 ≤ sectorMass s n - sectorBorn s e n at h1
  exact ⟨h0, by linarith⟩

theorem sectorBorn_summable (s : RawKernel) (e : NumberConservingEffect) :
    Summable (sectorBorn s e) :=
  Summable.of_nonneg_of_le (fun n => (sectorBorn_bounds s e n).1)
    (fun n => (sectorBorn_bounds s e n).2) (sectorMass_summable s)

def fullBorn (s : RawKernel) (e : NumberConservingEffect) : ℝ := ∑' n, sectorBorn s e n

def prefixBorn (s : RawKernel) (e : NumberConservingEffect) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (cutoff + 1), sectorBorn s e n

def omittedBorn (s : RawKernel) (e : NumberConservingEffect) (cutoff : ℕ) : ℝ :=
  ∑' n : ℕ, sectorBorn s e (n + (cutoff + 1))

theorem fullBorn_bounds (s : RawKernel) (e : NumberConservingEffect) :
    0 ≤ fullBorn s e ∧ fullBorn s e ≤ 1 := by
  refine ⟨tsum_nonneg fun n => (sectorBorn_bounds s e n).1, ?_⟩
  rw [← sectorMass_tsum s]
  exact (sectorBorn_summable s e).tsum_le_tsum
    (fun n => (sectorBorn_bounds s e n).2) (sectorMass_summable s)

theorem prefixBorn_add_omitted (s : RawKernel) (e : NumberConservingEffect) (cutoff : ℕ) :
    prefixBorn s e cutoff + omittedBorn s e cutoff = fullBorn s e :=
  (sectorBorn_summable s e).sum_add_tsum_nat_add (cutoff + 1)

theorem omittedBorn_bounds (s : RawKernel) (e : NumberConservingEffect) (cutoff : ℕ) :
    0 ≤ omittedBorn s e cutoff ∧ omittedBorn s e cutoff ≤ sourceTail s cutoff := by
  refine ⟨tsum_nonneg fun n => (sectorBorn_bounds s e (n + (cutoff + 1))).1, ?_⟩
  exact ((summable_nat_add_iff (cutoff + 1)).mpr (sectorBorn_summable s e)).tsum_le_tsum
    (fun n => (sectorBorn_bounds s e (n + (cutoff + 1))).2)
    ((summable_nat_add_iff (cutoff + 1)).mpr (sectorMass_summable s))

theorem born_truncation_budget (s : RawKernel) (e : NumberConservingEffect) (cutoff : ℕ) :
    0 ≤ fullBorn s e - prefixBorn s e cutoff ∧
      fullBorn s e - prefixBorn s e cutoff ≤ sourceTail s cutoff := by
  have heq : fullBorn s e - prefixBorn s e cutoff = omittedBorn s e cutoff := by
    linarith [prefixBorn_add_omitted s e cutoff]
  rw [heq]
  exact omittedBorn_bounds s e cutoff

def calibrationDen (N L A B : ℝ) : ℝ := N * L - A * B
def calibrationMean (N L A B : ℝ) : ℝ := A * B / calibrationDen N L A B
def calibrationTA (N L A B : ℝ) : ℝ := calibrationDen N L A B / (N * B)
def calibrationTB (N L A B : ℝ) : ℝ := calibrationDen N L A B / (N * A)
def calibrationRatio (N L A B : ℝ) : ℝ := A * B / (N * L)

theorem calibrationRatio_bounds {N L A B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hden : 0 < calibrationDen N L A B) :
    0 ≤ calibrationRatio N L A B ∧ calibrationRatio N L A B < 1 := by
  have hNL : 0 < N * L := mul_pos hN hL
  refine ⟨div_nonneg (mul_nonneg hA hB) hNL.le, (div_lt_one hNL).mpr ?_⟩
  dsimp [calibrationDen] at hden
  linarith

theorem calibration_mapping {N L A B : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hA : 0 < A) (hB : 0 < B) (hden : 0 < calibrationDen N L A B) :
    meanNumber (calibrationRatio N L A B) = calibrationMean N L A B ∧
      calibrationMean N L A B / (1 + calibrationMean N L A B) =
        calibrationRatio N L A B ∧
      N * calibrationMean N L A B * calibrationTA N L A B = A ∧
      N * calibrationMean N L A B * calibrationTB N L A B = B ∧
      N * calibrationMean N L A B * (1 + calibrationMean N L A B) *
        calibrationTA N L A B * calibrationTB N L A B = L := by
  have hn : N ≠ 0 := ne_of_gt hN
  have hl : L ≠ 0 := ne_of_gt hL
  have ha : A ≠ 0 := ne_of_gt hA
  have hb : B ≠ 0 := ne_of_gt hB
  have hd : calibrationDen N L A B ≠ 0 := ne_of_gt hden
  have ht : 1 - calibrationRatio N L A B ≠ 0 :=
    ne_of_gt (sub_pos.mpr (calibrationRatio_bounds hN hL hA.le hB.le hden).2)
  have hm : 1 + calibrationMean N L A B ≠ 0 := by
    have hm0 : 0 ≤ calibrationMean N L A B := div_nonneg (mul_nonneg hA.le hB.le) hden.le
    linarith
  dsimp [meanNumber, calibrationMean, calibrationTA, calibrationTB, calibrationRatio,
    calibrationDen] at *
  constructor
  · field_simp [hn, hl, hd, ht]
  constructor
  · field_simp [hn, hl, hd, hm]
    ring
  constructor
  · field_simp [hn, hb, hd]
  constructor
  · field_simp [hn, ha, hd]
  · field_simp [hn, ha, hb, hd]
    ring

def phaseFromCos (c : ℝ) : ℂ := ⟨c, Real.sqrt (1 - c ^ 2)⟩

theorem phaseFromCos_unit {c : ℝ} (hc : c ^ 2 ≤ 1) :
    Complex.normSq (phaseFromCos c) = 1 := by
  simp only [phaseFromCos, Complex.normSq_mk]
  rw [Real.mul_self_sqrt (sub_nonneg.mpr hc)]
  nlinarith

structure SevenSeed where
  H : ℝ
  V : ℝ
  X : ℝ
  AH : ℝ
  AV : ℝ
  BH : ℝ
  BV : ℝ

def sourceOfSeed (N : ℝ) (p : SevenSeed) (hN : 0 < N) (hH : 0 < p.H)
    (hV : 0 < p.V) (hAH : 0 ≤ p.AH) (hAV : 0 ≤ p.AV) (hBH : 0 ≤ p.BH)
    (hBV : 0 ≤ p.BV) (hdenH : 0 < calibrationDen N p.H p.AH p.BH)
    (hdenV : 0 < calibrationDen N p.V p.AV p.BV)
    (hphase : (p.X / Real.sqrt (p.H * p.V)) ^ 2 ≤ 1) : RawKernel where
  tH := calibrationRatio N p.H p.AH p.BH
  tV := calibrationRatio N p.V p.AV p.BV
  phase := phaseFromCos (p.X / Real.sqrt (p.H * p.V))
  tH_nonneg := (calibrationRatio_bounds hN hH hAH hBH hdenH).1
  tH_lt_one := (calibrationRatio_bounds hN hH hAH hBH hdenH).2
  tV_nonneg := (calibrationRatio_bounds hN hV hAV hBV hdenV).1
  tV_lt_one := (calibrationRatio_bounds hN hV hAV hBV hdenV).2
  phase_unit := phaseFromCos_unit hphase

end
end P23.GaussianWindow
