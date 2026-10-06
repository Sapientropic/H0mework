import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.EnvironmentSource.Sectorconsumer

set_option autoImplicit false

namespace P23.EnvironmentSource.Matched

open Matrix
open P23.GaussianWindow P23.GaussianWindow.NativeEffects
open P23.EnvironmentSource.Sector
open P23.EnvironmentSource.Sector.Consumer
open scoped BigOperators ComplexOrder
noncomputable section

def miss (d : EnvironmentPrim) : ℝ := 1 - d.detector.TV

theorem miss_bounds (d : EnvironmentPrim) : 0 ≤ miss d ∧ miss d ≤ 1 :=
  ⟨sub_nonneg.mpr d.detector.TV_le_one, by dsimp [miss]; linarith [d.detector.TV_nonneg]⟩

theorem matched_noClick (d : EnvironmentPrim) :
    noClickGram d 0 = diagonal (fun p : Bool => if p then (1 : ℂ) else (miss d : ℂ)) := by
  rw [noClick_complement, clickedGram_formula]
  ext i j
  cases i <;> cases j <;>
    simp [clickedFormula, miss]

theorem matched_gamma (d : EnvironmentPrim) (n : ℕ) :
    P23.EnvironmentSource.gamma d 0 n =
      diagonal (fun h : Fin (n + 1) => ((miss d : ℂ) ^ (n - h.val))) := by
  change symmetricPower (noClickGram d 0) n = _
  rw [matched_noClick, symmetricPower_diagonal]
  congr 1
  funext h
  simp [occupationWeight]

theorem matched_block (dA dB : EnvironmentPrim) (n : ℕ) :
    (environmentJointNoClick dA dB 0 0).block n =
      diagonal (fun h : Fin (n + 1) => (((miss dA * miss dB : ℝ) : ℂ) ^ (n - h.val))) := by
  change pairedBlock (P23.EnvironmentSource.gamma dA 0 n) (P23.EnvironmentSource.gamma dB 0 n) = _
  rw [matched_gamma, matched_gamma]
  ext h k
  by_cases hh : h = k
  · subst k
    simp [pairedBlock_apply, mul_pow]
  · simp [pairedBlock_apply, hh]

theorem matched_sector_mass (s : RawKernel) (dA dB : EnvironmentPrim) (n : ℕ) :
    sectorBorn s (environmentJointNoClick dA dB 0 0) n =
      ∑ h ∈ Finset.range (n + 1), numberMass s h (n - h) * (miss dA * miss dB) ^ (n - h) := by
  rw [sectorBorn, matched_block]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  change (∑ h : Fin (n + 1), star (sectorVector s n h) *
    ((((miss dA * miss dB : ℝ) : ℂ) ^ (n - h.val)) * sectorVector s n h)).re = _
  calc
    _ = (∑ h : Fin (n + 1),
        ((numberMass s h.val (n - h.val) * (miss dA * miss dB) ^ (n - h.val) : ℝ) : ℂ)).re := by
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      have hn : star (sectorVector s n h) * sectorVector s n h =
          (numberMass s h.val (n - h.val) : ℂ) := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        simp only [sectorVector, amplitude_normSq]
      push_cast
      rw [← hn]
      ring
    _ = ∑ h : Fin (n + 1), numberMass s h.val (n - h.val) *
        (miss dA * miss dB) ^ (n - h.val) := by norm_cast
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun h : ℕ => numberMass s h (n - h) * (miss dA * miss dB) ^ (n - h)) (n + 1)

theorem product_miss_bounds (dA dB : EnvironmentPrim) :
    0 ≤ miss dA * miss dB ∧ miss dA * miss dB ≤ 1 := by
  refine ⟨mul_nonneg (miss_bounds dA).1 (miss_bounds dB).1, ?_⟩
  exact (mul_le_mul_of_nonneg_right (miss_bounds dA).2 (miss_bounds dB).1).trans
    (by simpa using (miss_bounds dB).2)

theorem weighted_number_cauchy (s : RawKernel) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑' n : ℕ, ∑ h ∈ Finset.range (n + 1), numberMass s h (n - h) * z ^ (n - h)) =
      (1 - s.tV) / (1 - s.tV * z) := by
  have htz : s.tV * z < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right s.tV_nonneg hz1) s.tV_lt_one
  have hH := geometricMass_hasSum s.tH_nonneg s.tH_lt_one
  have hV := geometricMass_weighted_hasSum s.tV_nonneg hz0 htz
  have hp : Summable (fun hv : ℕ × ℕ =>
      geometricMass s.tH hv.1 * (geometricMass s.tV hv.2 * z ^ hv.2)) := by
    simpa only [numberMass, one_pow, mul_one, mul_assoc] using
      (countPGF_hasSum s (zH := 1) (zV := z) (by positivity) hz0 (by simpa using s.tH_lt_one) htz).summable
  have hc := Summable.tsum_mul_tsum_eq_tsum_sum_range hH.summable hV.summable hp
  calc
    _ = ∑' n : ℕ, ∑ h ∈ Finset.range (n + 1),
        geometricMass s.tH h * (geometricMass s.tV (n - h) * z ^ (n - h)) := by
      congr 1
      funext n
      apply Finset.sum_congr rfl
      intro h _
      dsimp only [numberMass]
      ring
    _ = (∑' h, geometricMass s.tH h) * (∑' v, geometricMass s.tV v * z ^ v) := hc.symm
    _ = _ := by rw [hH.tsum_eq, hV.tsum_eq, one_mul]

theorem matched_fullBorn (s : RawKernel) (dA dB : EnvironmentPrim) :
    fullBorn s (environmentJointNoClick dA dB 0 0) =
      (1 - s.tV) / (1 - s.tV * miss dA * miss dB) := by
  simp only [fullBorn, matched_sector_mass]
  rw [weighted_number_cauchy s (miss dA * miss dB)
    (product_miss_bounds dA dB).1 (product_miss_bounds dA dB).2]
  congr 1
  ring

def silent : EnvironmentPrim where
  detector := ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  xi := 1
  xi_bound := by norm_num

def noClickA (s : RawKernel) (dA : EnvironmentPrim) : ℝ :=
  fullBorn s (environmentJointNoClick dA silent 0 0)

def noClickB (s : RawKernel) (dB : EnvironmentPrim) : ℝ :=
  fullBorn s (environmentJointNoClick silent dB 0 0)

def noClickAB (s : RawKernel) (dA dB : EnvironmentPrim) : ℝ :=
  fullBorn s (environmentJointNoClick dA dB 0 0)

def meanV (s : RawKernel) : ℝ := meanNumber s.tV

theorem meanV_nonneg (s : RawKernel) : 0 ≤ meanV s :=
  div_nonneg s.tV_nonneg (sub_nonneg.mpr s.tV_lt_one.le)

theorem meanV_pos (s : RawKernel) (ht : 0 < s.tV) : 0 < meanV s :=
  div_pos ht (sub_pos.mpr s.tV_lt_one)

theorem union_transmission_bounds (dA dB : EnvironmentPrim) :
    0 ≤ dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV ∧
      dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV ≤ 1 := by
  have h := product_miss_bounds dA dB
  dsimp only [miss] at h
  constructor <;> nlinarith [h.1, h.2]

theorem matched_mean_form (s : RawKernel) (dA dB : EnvironmentPrim) :
    noClickAB s dA dB =
      1 / (1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV)) := by
  rw [noClickAB, matched_fullBorn]
  have ht : 1 - s.tV ≠ 0 := ne_of_gt (sub_pos.mpr s.tV_lt_one)
  have hrel : 1 + meanV s *
      (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV) =
      (1 - s.tV * miss dA * miss dB) / (1 - s.tV) := by
    dsimp only [meanV, meanNumber, miss]
    field_simp [ht]
    ring
  rw [hrel, one_div_div]

theorem localA_mean_form (s : RawKernel) (dA : EnvironmentPrim) :
    noClickA s dA = 1 / (1 + meanV s * dA.detector.TV) := by
  have h := matched_mean_form s dA silent
  simpa [noClickA, noClickAB, silent] using h

theorem localB_mean_form (s : RawKernel) (dB : EnvironmentPrim) :
    noClickB s dB = 1 / (1 + meanV s * dB.detector.TV) := by
  have h := matched_mean_form s silent dB
  simpa [noClickB, noClickAB, silent] using h

structure BackgroundPrim where
  bA : ℝ
  bB : ℝ
  bA_nonneg : 0 ≤ bA
  bB_nonneg : 0 ≤ bB
  bA_lt_one : bA < 1
  bB_lt_one : bB < 1

def singleA (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) : ℝ :=
  1 - (1 - bg.bA) * noClickA s dA

def singleB (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) : ℝ :=
  1 - (1 - bg.bB) * noClickB s dB

def joint (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim) : ℝ :=
  1 - (1 - bg.bA) * noClickA s dA - (1 - bg.bB) * noClickB s dB +
    (1 - bg.bA) * (1 - bg.bB) * noClickAB s dA dB

def rawKA (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim) : Option ℝ :=
  if 0 < singleB s dB bg then some (joint s dA dB bg / singleB s dB bg) else none

def rawKB (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim) : Option ℝ :=
  if 0 < singleA s dA bg then some (joint s dA dB bg / singleA s dA bg) else none

theorem local_den_pos (s : RawKernel) (d : EnvironmentPrim) : 0 < 1 + meanV s * d.detector.TV := by
  nlinarith [mul_nonneg (meanV_nonneg s) d.detector.TV_nonneg]

theorem singleA_form (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) :
    singleA s dA bg = (bg.bA + meanV s * dA.detector.TV) / (1 + meanV s * dA.detector.TV) := by
  rw [singleA, localA_mean_form]
  field_simp [ne_of_gt (local_den_pos s dA)]
  ring

theorem singleB_form (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) :
    singleB s dB bg = (bg.bB + meanV s * dB.detector.TV) / (1 + meanV s * dB.detector.TV) := by
  rw [singleB, localB_mean_form]
  field_simp [ne_of_gt (local_den_pos s dB)]
  ring

theorem singleA_lt_one (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) :
    singleA s dA bg < 1 := by
  rw [singleA_form]
  exact (div_lt_one (local_den_pos s dA)).mpr (by linarith [bg.bA_lt_one])

theorem singleB_lt_one (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) :
    singleB s dB bg < 1 := by
  rw [singleB_form]
  exact (div_lt_one (local_den_pos s dB)).mpr (by linarith [bg.bB_lt_one])

theorem herald_A_iff (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) :
    0 < singleA s dA bg ↔ 0 < bg.bA ∨ (0 < s.tV ∧ 0 < dA.detector.TV) := by
  rw [singleA_form, div_pos_iff_of_pos_right (local_den_pos s dA)]
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hb : bg.bA = 0 := le_antisymm h.1 bg.bA_nonneg
    by_cases ht : 0 < s.tV
    · have hT : dA.detector.TV = 0 := le_antisymm (h.2 ht) dA.detector.TV_nonneg
      simp [hb, hT] at hp
    · have ht0 : s.tV = 0 := le_antisymm (le_of_not_gt ht) s.tV_nonneg
      simp [hb, meanV, meanNumber, ht0] at hp
  · rintro (hb | ⟨ht, hT⟩)
    · nlinarith [mul_nonneg (meanV_nonneg s) dA.detector.TV_nonneg]
    · have hp := mul_pos (meanV_pos s ht) hT
      linarith [bg.bA_nonneg]

theorem herald_B_iff (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) :
    0 < singleB s dB bg ↔ 0 < bg.bB ∨ (0 < s.tV ∧ 0 < dB.detector.TV) := by
  rw [singleB_form, div_pos_iff_of_pos_right (local_den_pos s dB)]
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hb : bg.bB = 0 := le_antisymm h.1 bg.bB_nonneg
    by_cases ht : 0 < s.tV
    · have hT : dB.detector.TV = 0 := le_antisymm (h.2 ht) dB.detector.TV_nonneg
      simp [hb, hT] at hp
    · have ht0 : s.tV = 0 := le_antisymm (le_of_not_gt ht) s.tV_nonneg
      simp [hb, meanV, meanNumber, ht0] at hp
  · rintro (hb | ⟨ht, hT⟩)
    · nlinarith [mul_nonneg (meanV_nonneg s) dB.detector.TV_nonneg]
    · have hp := mul_pos (meanV_pos s ht) hT
      linarith [bg.bB_nonneg]

theorem lossA_inverse (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) (ht : 0 < s.tV) :
    dA.detector.TV = (singleA s dA bg - bg.bA) / (meanV s * (1 - singleA s dA bg)) := by
  have hn := meanV_pos s ht
  have hl := singleA_lt_one s dA bg
  have hd : meanV s * (1 - singleA s dA bg) ≠ 0 := ne_of_gt (mul_pos hn (sub_pos.mpr hl))
  have hs : singleA s dA bg * (1 + meanV s * dA.detector.TV) = bg.bA + meanV s * dA.detector.TV := by
    rw [singleA_form, div_mul_cancel₀ _ (ne_of_gt (local_den_pos s dA))]
  apply (eq_div_iff hd).mpr
  nlinarith [hs]

theorem lossB_inverse (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) (ht : 0 < s.tV) :
    dB.detector.TV = (singleB s dB bg - bg.bB) / (meanV s * (1 - singleB s dB bg)) := by
  have hn := meanV_pos s ht
  have hl := singleB_lt_one s dB bg
  have hd : meanV s * (1 - singleB s dB bg) ≠ 0 := ne_of_gt (mul_pos hn (sub_pos.mpr hl))
  have hs : singleB s dB bg * (1 + meanV s * dB.detector.TV) = bg.bB + meanV s * dB.detector.TV := by
    rw [singleB_form, div_mul_cancel₀ _ (ne_of_gt (local_den_pos s dB))]
  apply (eq_div_iff hd).mpr
  nlinarith [hs]

def calibrationQ (n bA bB r a : ℝ) : ℝ :=
  (1 - bA - bB - bA * bB / n) +
    (bA * r + bB + (bB + r * bA) / n) * a - r * (1 + 1 / n) * a ^ 2

def calibrationP (n bA bB kA kB a : ℝ) : ℝ :=
  (1 - (1 + kB / kA - kB) * a) * calibrationQ n bA bB (kB / kA) a -
    (1 - bA) * (1 - bB) * (1 - a) * (1 - kB / kA * a)

def opticalJoint (s : RawKernel) (dA dB : EnvironmentPrim) : ℝ :=
  1 - noClickA s dA - noClickB s dB + noClickAB s dA dB

theorem union_den_pos (s : RawKernel) (dA dB : EnvironmentPrim) :
    0 < 1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV) := by
  nlinarith [mul_nonneg (meanV_nonneg s) (union_transmission_bounds dA dB).1]

theorem opticalJoint_form (s : RawKernel) (dA dB : EnvironmentPrim) :
    opticalJoint s dA dB =
      (meanV s * dA.detector.TV * dB.detector.TV *
        (1 + meanV s + meanV s *
          (1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV)))) /
      ((1 + meanV s * dA.detector.TV) * (1 + meanV s * dB.detector.TV) *
        (1 + meanV s * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV))) := by
  rw [opticalJoint, localA_mean_form, localB_mean_form, matched_mean_form]
  have hA := ne_of_gt (local_den_pos s dA)
  have hB := ne_of_gt (local_den_pos s dB)
  have hU := ne_of_gt (union_den_pos s dA dB)
  field_simp
  ring

theorem opticalJoint_pos (s : RawKernel) (dA dB : EnvironmentPrim)
    (ht : 0 < s.tV) (hA : 0 < dA.detector.TV) (hB : 0 < dB.detector.TV) :
    0 < opticalJoint s dA dB := by
  rw [opticalJoint_form]
  have hn := meanV_pos s ht
  have hU := union_den_pos s dA dB
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos hn hA) hB)
      (by nlinarith [mul_pos hn hU])
  · exact mul_pos (mul_pos (local_den_pos s dA) (local_den_pos s dB)) hU

theorem background_joint_split (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim) :
    joint s dA dB bg = bg.bA * bg.bB +
      bg.bA * (1 - bg.bB) * (1 - noClickB s dB) +
      bg.bB * (1 - bg.bA) * (1 - noClickA s dA) +
      (1 - bg.bA) * (1 - bg.bB) * opticalJoint s dA dB := by
  dsimp only [joint, opticalJoint]
  ring

theorem joint_pos (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim)
    (ht : 0 < s.tV) (hA : 0 < dA.detector.TV) (hB : 0 < dB.detector.TV) :
    0 < joint s dA dB bg := by
  have hqa : 0 ≤ 1 - noClickA s dA :=
    sub_nonneg.mpr (fullBorn_bounds s (environmentJointNoClick dA silent 0 0)).2
  have hqb : 0 ≤ 1 - noClickB s dB :=
    sub_nonneg.mpr (fullBorn_bounds s (environmentJointNoClick silent dB 0 0)).2
  have hba := sub_pos.mpr bg.bA_lt_one
  have hbb := sub_pos.mpr bg.bB_lt_one
  rw [background_joint_split]
  have h1 := mul_nonneg bg.bA_nonneg bg.bB_nonneg
  have h2 := mul_nonneg (mul_nonneg bg.bA_nonneg hbb.le) hqb
  have h3 := mul_nonneg (mul_nonneg bg.bB_nonneg hba.le) hqa
  have h4 := mul_pos (mul_pos hba hbb) (opticalJoint_pos s dA dB ht hA hB)
  linarith

theorem singleA_relation (s : RawKernel) (dA : EnvironmentPrim) (bg : BackgroundPrim) :
    meanV s * dA.detector.TV * (1 - singleA s dA bg) = singleA s dA bg - bg.bA := by
  have hs : singleA s dA bg * (1 + meanV s * dA.detector.TV) = bg.bA + meanV s * dA.detector.TV := by
    rw [singleA_form, div_mul_cancel₀ _ (ne_of_gt (local_den_pos s dA))]
  nlinarith [hs]

theorem singleB_relation (s : RawKernel) (dB : EnvironmentPrim) (bg : BackgroundPrim) :
    meanV s * dB.detector.TV * (1 - singleB s dB bg) = singleB s dB bg - bg.bB := by
  have hs : singleB s dB bg * (1 + meanV s * dB.detector.TV) = bg.bB + meanV s * dB.detector.TV := by
    rw [singleB_form, div_mul_cancel₀ _ (ne_of_gt (local_den_pos s dB))]
  nlinarith [hs]

theorem generated_cubic (s : RawKernel) (dA dB : EnvironmentPrim) (bg : BackgroundPrim)
    (ht : 0 < s.tV) (hA : 0 < dA.detector.TV) (hB : 0 < dB.detector.TV) :
    calibrationP (meanV s) bg.bA bg.bB (joint s dA dB bg / singleB s dB bg)
      (joint s dA dB bg / singleA s dA bg) (singleA s dA bg) = 0 := by
  let n := meanV s
  let a := singleA s dA bg
  let b := singleB s dB bg
  let j := joint s dA dB bg
  let U := 1 + n * (dA.detector.TV + dB.detector.TV - dA.detector.TV * dB.detector.TV)
  have hn : n ≠ 0 := ne_of_gt (meanV_pos s ht)
  have ha : a ≠ 0 := ne_of_gt ((herald_A_iff s dA bg).mpr (Or.inr ⟨ht, hA⟩))
  have hb : b ≠ 0 := ne_of_gt ((herald_B_iff s dB bg).mpr (Or.inr ⟨ht, hB⟩))
  have hj : j ≠ 0 := ne_of_gt (joint_pos s dA dB bg ht hA hB)
  have hr : (j / a) / (j / b) = b / a := by field_simp
  have hsa : n * dA.detector.TV * (1 - a) = a - bg.bA := singleA_relation s dA bg
  have hsb : n * dB.detector.TV * (1 - b) = b - bg.bB := singleB_relation s dB bg
  have hq : calibrationQ n bg.bA bg.bB (b / a) a = (1 - a) * (1 - b) * U := by
    calc
      _ = (1 - a) * (1 - b) + (a - bg.bA) * (1 - b) +
          (b - bg.bB) * (1 - a) - (a - bg.bA) * (b - bg.bB) / n := by
        dsimp only [calibrationQ]
        field_simp
        ring
      _ = _ := by
        rw [← hsa, ← hsb]
        dsimp only [U]
        field_simp
        ring
  have hw : 1 - (1 + b / a - j / a) * a =
      (1 - bg.bA) * (1 - bg.bB) * noClickAB s dA dB := by
    calc
      _ = 1 - a - b + j := by field_simp; ring
      _ = _ := by dsimp only [a, b, j, singleA, singleB, joint]; ring
  have hqu : noClickAB s dA dB * U = 1 := by
    rw [matched_mean_form]
    exact div_mul_cancel₀ _ (ne_of_gt (union_den_pos s dA dB))
  change calibrationP n bg.bA bg.bB (j / b) (j / a) a = 0
  rw [calibrationP, hr, hq, hw, div_mul_cancel₀ _ ha]
  calc
    _ = (1 - bg.bA) * (1 - bg.bB) * (1 - a) * (1 - b) *
        (noClickAB s dA dB * U - 1) := by ring
    _ = 0 := by rw [hqu]; ring

end
end P23.EnvironmentSource.Matched
