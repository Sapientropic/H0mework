import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.Gaussiansource
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic

/-!
Raw losses and a V-reference angle generate the clicked, perpendicular and two
lost ports. Their complete Gram is the identity. All photon-number effects use
explicit word tensors and normalized occupation columns; no positivity or
occupation isometry is supplied by the caller. Bool true is H throughout.
-/

set_option autoImplicit false

namespace P23.GaussianWindow.NativeEffects

open Matrix
open scoped BigOperators ComplexOrder Kronecker
noncomputable section

structure DetectorPrim where
  TH : ℝ
  TV : ℝ
  TH_nonneg : 0 ≤ TH
  TH_le_one : TH ≤ 1
  TV_nonneg : 0 ≤ TV
  TV_le_one : TV ≤ 1

def clickRow (d : DetectorPrim) (a : ℝ) (p : Bool) : ℂ :=
  ((if p then Real.sqrt d.TH * Real.sin a else Real.sqrt d.TV * Real.cos a) : ℝ)

def perpendicularRow (d : DetectorPrim) (a : ℝ) (p : Bool) : ℂ :=
  ((if p then Real.sqrt d.TH * Real.cos a else -(Real.sqrt d.TV * Real.sin a)) : ℝ)

def lostHRow (d : DetectorPrim) (p : Bool) : ℂ :=
  ((if p then Real.sqrt (1 - d.TH) else 0) : ℝ)

def lostVRow (d : DetectorPrim) (p : Bool) : ℂ :=
  ((if p then 0 else Real.sqrt (1 - d.TV)) : ℝ)

def ports (d : DetectorPrim) (a : ℝ) : Matrix (Fin 4) Bool ℂ :=
  ![clickRow d a, perpendicularRow d a, lostHRow d, lostVRow d]

def noClickPorts (d : DetectorPrim) (a : ℝ) : Matrix (Fin 3) Bool ℂ :=
  (ports d a).submatrix Fin.succ id

def clickedPorts (d : DetectorPrim) (a : ℝ) : Matrix (Fin 1) Bool ℂ :=
  fun _ => clickRow d a

def onePhotonEffect (d : DetectorPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  (noClickPorts d a)ᴴ * noClickPorts d a

def transmissionRoot (d : DetectorPrim) : Matrix Bool Bool ℂ :=
  diagonal fun p => ((if p then Real.sqrt d.TH else Real.sqrt d.TV) : ℝ)

def analyzerVector (a : ℝ) (p : Bool) : ℂ :=
  ((if p then Real.sin a else Real.cos a) : ℝ)

theorem ports_gram (d : DetectorPrim) (a : ℝ) : (ports d a)ᴴ * ports d a = 1 := by
  have hH := Real.mul_self_sqrt d.TH_nonneg
  have hV := Real.mul_self_sqrt d.TV_nonneg
  have hLH := Real.mul_self_sqrt (sub_nonneg.mpr d.TH_le_one)
  have hLV := Real.mul_self_sqrt (sub_nonneg.mpr d.TV_le_one)
  have hu := Real.sin_sq_add_cos_sq a
  ext i j
  change (∑ k : Fin 4, star (ports d a k i) * ports d a k j) = if i = j then 1 else 0
  cases i <;> cases j <;>
    simp [ports, clickRow, perpendicularRow, lostHRow, lostVRow, Fin.sum_univ_succ,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
  all_goals norm_cast
  case false.false =>
    linear_combination (Real.sin a) ^ 2 * hV + (Real.cos a) ^ 2 * hV + hLV + d.TV * hu
  case false.true => ring
  case true.false => ring
  case true.true =>
    linear_combination (Real.sin a) ^ 2 * hH + (Real.cos a) ^ 2 * hH + hLH + d.TH * hu

theorem ports_gram_split (d : DetectorPrim) (a : ℝ) :
    (ports d a)ᴴ * ports d a =
      (clickedPorts d a)ᴴ * clickedPorts d a + onePhotonEffect d a := by
  ext i j
  change (∑ k : Fin 4, star (ports d a k i) * ports d a k j) =
    (∑ k : Fin 1, star (clickedPorts d a k i) * clickedPorts d a k j) +
      ∑ k : Fin 3, star (noClickPorts d a k i) * noClickPorts d a k j
  simp [Fin.sum_univ_succ, ports, clickedPorts, noClickPorts, Matrix.submatrix]

theorem onePhoton_complement (d : DetectorPrim) (a : ℝ) :
    1 - onePhotonEffect d a = (clickedPorts d a)ᴴ * clickedPorts d a := by
  have h := ports_gram_split d a
  rw [ports_gram] at h
  rw [h]
  abel

theorem clicked_gram_form (d : DetectorPrim) (a : ℝ) :
    (clickedPorts d a)ᴴ * clickedPorts d a = transmissionRoot d *
      vecMulVec (analyzerVector a) (star (analyzerVector a)) * transmissionRoot d := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  dsimp only [transmissionRoot]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases i <;> cases j <;>
    simp [clickedPorts, clickRow, analyzerVector, vecMulVec,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;> ring

theorem onePhoton_form (d : DetectorPrim) (a : ℝ) :
    onePhotonEffect d a = 1 - transmissionRoot d *
      vecMulVec (analyzerVector a) (star (analyzerVector a)) * transmissionRoot d := by
  rw [← clicked_gram_form, ← onePhoton_complement]
  abel

theorem onePhoton_bounds (d : DetectorPrim) (a : ℝ) :
    (onePhotonEffect d a).PosSemidef ∧ (1 - onePhotonEffect d a).PosSemidef := by
  refine ⟨posSemidef_conjTranspose_mul_self (noClickPorts d a), ?_⟩
  rw [onePhoton_complement]
  exact posSemidef_conjTranspose_mul_self (clickedPorts d a)

abbrev Words (n : ℕ) (I : Type*) := Fin n → I

def wordSplit (n : ℕ) (I : Type*) : Words (n + 1) I ≃ I × Words n I where
  toFun w := (w 0, Fin.tail w)
  invFun w := Fin.cons w.1 w.2
  left_inv w := Fin.cons_self_tail w
  right_inv w := by cases w; simp

def wordTensor {I J : Type*} (M : Matrix I J ℂ) (n : ℕ) :
    Matrix (Words n I) (Words n J) ℂ :=
  fun w z => ∏ i : Fin n, M (w i) (z i)

theorem wordTensor_succ {I J : Type*} (M : Matrix I J ℂ) (n : ℕ) :
    wordTensor M (n + 1) =
      (M ⊗ₖ wordTensor M n).submatrix (wordSplit n I) (wordSplit n J) := by
  ext w z
  simp [wordTensor, wordSplit, Fin.prod_univ_succ, Fin.tail]

theorem wordTensor_conjTranspose {I J : Type*} (M : Matrix I J ℂ) (n : ℕ) :
    wordTensor Mᴴ n = (wordTensor M n)ᴴ := by
  ext w z
  simp [wordTensor, Matrix.conjTranspose_apply]

theorem wordTensor_mul {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : Matrix I J ℂ) (B : Matrix J K ℂ) (n : ℕ) :
    wordTensor (A * B) n = wordTensor A n * wordTensor B n := by
  induction n with
  | zero =>
      ext w z
      simp [wordTensor, Matrix.mul_apply]
  | succ n ih =>
      rw [wordTensor_succ, ih, Matrix.mul_kronecker_mul,
        wordTensor_succ A, wordTensor_succ B, Matrix.submatrix_mul_equiv]

theorem wordTensor_zero {I : Type*} [DecidableEq I] (E : Matrix I I ℂ) :
    wordTensor E 0 = 1 := by
  ext w z
  have hwz : w = z := Subsingleton.elim _ _
  simp [wordTensor, Matrix.one_apply, hwz]

theorem wordTensor_one {I : Type*} [DecidableEq I] (n : ℕ) :
    wordTensor (1 : Matrix I I ℂ) n = 1 := by
  induction n with
  | zero => exact wordTensor_zero 1
  | succ n ih =>
      rw [wordTensor_succ, ih, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem complement_kronecker {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    1 - A ⊗ₖ B = (1 - A) ⊗ₖ B + (1 : Matrix I I ℂ) ⊗ₖ (1 - B) := by
  rw [← Matrix.one_kronecker_one]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kronecker_apply]
  ring

theorem kronecker_bounds {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef)
    (hB : B.PosSemidef) (hBc : (1 - B).PosSemidef) :
    (A ⊗ₖ B).PosSemidef ∧ (1 - A ⊗ₖ B).PosSemidef := by
  refine ⟨hA.kronecker hB, ?_⟩
  rw [complement_kronecker]
  exact (hAc.kronecker hB).add (PosSemidef.one.kronecker hBc)

theorem wordTensor_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {E : Matrix I I ℂ} (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef) (n : ℕ) :
    (wordTensor E n).PosSemidef ∧ (1 - wordTensor E n).PosSemidef := by
  induction n with
  | zero => simp only [wordTensor_zero, sub_self]; exact ⟨PosSemidef.one, PosSemidef.zero⟩
  | succ n ih =>
      have h := kronecker_bounds hE hEc ih.1 ih.2
      rw [wordTensor_succ]
      refine ⟨h.1.submatrix (wordSplit n I), ?_⟩
      have hc := h.2.submatrix (wordSplit n I)
      have heq : (1 - E ⊗ₖ wordTensor E n).submatrix (wordSplit n I) (wordSplit n I) =
          1 - (E ⊗ₖ wordTensor E n).submatrix (wordSplit n I) (wordSplit n I) := by
        calc
          _ = (1 : Matrix (I × Words n I) (I × Words n I) ℂ).submatrix
              (wordSplit n I) (wordSplit n I) -
                (E ⊗ₖ wordTensor E n).submatrix (wordSplit n I) (wordSplit n I) := rfl
          _ = _ := by rw [Matrix.submatrix_one_equiv]
      rw [heq] at hc
      exact hc

def hSupport {n : ℕ} (w : Words n Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i = true

def countH {n : ℕ} (w : Words n Bool) : ℕ := (hSupport w).card

def wordSupportEquiv (n : ℕ) : Words n Bool ≃ Finset (Fin n) where
  toFun := hSupport
  invFun S := fun i => decide (i ∈ S)
  left_inv w := by
    funext i
    cases h : w i <;> simp [hSupport, h]
  right_inv S := by
    ext i
    simp [hSupport]

theorem fiber_sum (n h : ℕ) :
    (∑ w : Words n Bool, if countH w = h then (1 : ℂ) else 0) = (n.choose h : ℂ) := by
  calc
    (∑ w : Words n Bool, if countH w = h then (1 : ℂ) else 0) =
        ∑ S : Finset (Fin n), if S.card = h then (1 : ℂ) else 0 :=
      Fintype.sum_equiv (wordSupportEquiv n) _ _ (fun _ => rfl)
    _ = (n.choose h : ℂ) := by
      rw [← Finset.sum_filter]
      simp [Finset.univ_filter_card_eq, Finset.card_powersetCard]

def occupationCoeff (n : ℕ) (h : Fin (n + 1)) : ℂ :=
  ((Real.sqrt (n.choose h.val : ℝ))⁻¹ : ℝ)

def occupation (n : ℕ) : Matrix (Words n Bool) (Fin (n + 1)) ℂ :=
  fun w h => if countH w = h.val then occupationCoeff n h else 0

theorem occupationCoeff_norm (n : ℕ) (h : Fin (n + 1)) :
    (n.choose h.val : ℂ) * occupationCoeff n h ^ 2 = 1 := by
  have hp : 0 < (n.choose h.val : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hs : Real.sqrt (n.choose h.val : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hr : (n.choose h.val : ℝ) * (Real.sqrt (n.choose h.val : ℝ))⁻¹ ^ 2 = 1 := by
    calc
      _ = (Real.sqrt (n.choose h.val : ℝ)) ^ 2 *
          (Real.sqrt (n.choose h.val : ℝ))⁻¹ ^ 2 := by rw [Real.sq_sqrt hp.le]
      _ = 1 := by field_simp [hs]
  dsimp [occupationCoeff]
  exact_mod_cast hr

theorem occupation_diagonal (n : ℕ) (h : Fin (n + 1)) :
    (∑ w : Words n Bool, star (occupation n w h) * occupation n w h) = 1 := by
  calc
    _ = (n.choose h.val : ℂ) * occupationCoeff n h ^ 2 := by
      rw [← fiber_sum n h.val, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : countH w = h.val <;>
        simp [occupation, occupationCoeff, hw, pow_two]
    _ = 1 := occupationCoeff_norm n h

theorem occupation_isometry (n : ℕ) : (occupation n)ᴴ * occupation n = 1 := by
  ext h k
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases hhk : h = k
  · subst k
    rw [occupation_diagonal]
    simp
  · have hzero : (∑ w : Words n Bool, star (occupation n w h) * occupation n w k) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : countH w = h.val
      · have hval : h.val ≠ k.val := fun hk => hhk (Fin.ext hk)
        simp [occupation, hw, hval]
      · simp [occupation, hw]
    rw [hzero]
    simp [hhk]

def gamma (d : DetectorPrim) (a : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (occupation n)ᴴ * wordTensor (onePhotonEffect d a) n * occupation n

theorem gamma_port_born (d : DetectorPrim) (a : ℝ) (n : ℕ) :
    gamma d a n =
      (wordTensor (noClickPorts d a) n * occupation n)ᴴ *
        (wordTensor (noClickPorts d a) n * occupation n) := by
  simp only [gamma, onePhotonEffect, wordTensor_mul, wordTensor_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem gamma_bounds (d : DetectorPrim) (a : ℝ) (n : ℕ) :
    (gamma d a n).PosSemidef ∧ (1 - gamma d a n).PosSemidef := by
  have h := wordTensor_bounds (onePhoton_bounds d a).1 (onePhoton_bounds d a).2 n
  refine ⟨h.1.conjTranspose_mul_mul_same (occupation n), ?_⟩
  have heq : (occupation n)ᴴ * (1 - wordTensor (onePhotonEffect d a) n) * occupation n =
      1 - gamma d a n := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, occupation_isometry, gamma]
  rw [← heq]
  exact h.2.conjTranspose_mul_mul_same (occupation n)

def pairedIndex (n : ℕ) (h : Fin (n + 1)) : Fin (n + 1) × Fin (n + 1) := (h, h)

theorem pairedIndex_injective (n : ℕ) : Function.Injective (pairedIndex n) := by
  intro h k hk
  exact congrArg Prod.fst hk

def pairedBlock {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (A ⊗ₖ B).submatrix (pairedIndex n) (pairedIndex n)

theorem pairedBlock_apply {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h k : Fin (n + 1)) : pairedBlock A B h k = A h k * B h k := rfl

theorem pairedBlock_bounds {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef)
    (hB : B.PosSemidef) (hBc : (1 - B).PosSemidef) :
    (pairedBlock A B).PosSemidef ∧ (1 - pairedBlock A B).PosSemidef := by
  have h := kronecker_bounds hA hAc hB hBc
  refine ⟨h.1.submatrix (pairedIndex n), ?_⟩
  have hc := h.2.submatrix (pairedIndex n)
  have heq : (1 - A ⊗ₖ B).submatrix (pairedIndex n) (pairedIndex n) = 1 - pairedBlock A B := by
    calc
      _ = (1 : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ).submatrix
          (pairedIndex n) (pairedIndex n) - (A ⊗ₖ B).submatrix (pairedIndex n) (pairedIndex n) := rfl
      _ = _ := by rw [Matrix.submatrix_one _ (pairedIndex_injective n)]; rfl
  rw [heq] at hc
  exact hc

def aliceNoClick (d : DetectorPrim) (a : ℝ) : NumberConservingEffect where
  block n := pairedBlock (gamma d a n) 1
  positive n := (pairedBlock_bounds (gamma_bounds d a n).1 (gamma_bounds d a n).2
    PosSemidef.one (by simp only [sub_self]; exact PosSemidef.zero)).1
  complement_positive n :=
    (pairedBlock_bounds (gamma_bounds d a n).1 (gamma_bounds d a n).2
      PosSemidef.one (by simp only [sub_self]; exact PosSemidef.zero)).2

def bobNoClick (d : DetectorPrim) (b : ℝ) : NumberConservingEffect where
  block n := pairedBlock 1 (gamma d b n)
  positive n := (pairedBlock_bounds PosSemidef.one (by simp only [sub_self]; exact PosSemidef.zero)
    (gamma_bounds d b n).1 (gamma_bounds d b n).2).1
  complement_positive n :=
    (pairedBlock_bounds PosSemidef.one (by simp only [sub_self]; exact PosSemidef.zero)
      (gamma_bounds d b n).1 (gamma_bounds d b n).2).2

def jointNoClick (dA dB : DetectorPrim) (a b : ℝ) : NumberConservingEffect where
  block n := pairedBlock (gamma dA a n) (gamma dB b n)
  positive n := (pairedBlock_bounds (gamma_bounds dA a n).1 (gamma_bounds dA a n).2
    (gamma_bounds dB b n).1 (gamma_bounds dB b n).2).1
  complement_positive n :=
    (pairedBlock_bounds (gamma_bounds dA a n).1 (gamma_bounds dA a n).2
      (gamma_bounds dB b n).1 (gamma_bounds dB b n).2).2

theorem aliceNoClick_apply (d : DetectorPrim) (a : ℝ) (n : ℕ) (h k : Fin (n + 1)) :
    (aliceNoClick d a).block n h k = if h = k then gamma d a n h h else 0 := by
  simp only [aliceNoClick, pairedBlock_apply, Matrix.one_apply]
  split_ifs with hk
  · subst k; simp
  · simp

theorem bobNoClick_apply (d : DetectorPrim) (b : ℝ) (n : ℕ) (h k : Fin (n + 1)) :
    (bobNoClick d b).block n h k = if h = k then gamma d b n h h else 0 := by
  simp only [bobNoClick, pairedBlock_apply, Matrix.one_apply]
  split_ifs with hk
  · subst k; simp
  · simp

theorem jointNoClick_apply (dA dB : DetectorPrim) (a b : ℝ) (n : ℕ) (h k : Fin (n + 1)) :
    (jointNoClick dA dB a b).block n h k = gamma dA a n h k * gamma dB b n h k := rfl

end
end P23.GaussianWindow.NativeEffects
