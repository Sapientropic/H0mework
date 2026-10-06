import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.EnvironmentSource.Environmentsource
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace P23.EnvironmentSource.Sector

open Matrix
open P23.GaussianWindow P23.GaussianWindow.NativeEffects
open scoped BigOperators ComplexOrder
noncomputable section

theorem countH_le {n : ℕ} (w : Words n Bool) : countH w ≤ n := by
  simpa only [countH, Fintype.card_fin] using Finset.card_le_univ (hSupport w)

theorem fiber_true_card {n : ℕ} (w : Words n Bool) :
    Fintype.card {i : Fin n // w i = true} = countH w := by
  rw [Fintype.card_subtype]
  rfl

theorem fiber_false_card {n : ℕ} (w : Words n Bool) :
    Fintype.card {i : Fin n // w i = false} = n - countH w := by
  have h : {i : Fin n // w i = false} ≃ {i : Fin n // ¬w i = true} :=
    Equiv.subtypeEquivRight fun i => by cases w i <;> simp
  rw [Fintype.card_congr h, Fintype.card_subtype_compl, Fintype.card_fin, fiber_true_card]

def matchingPerm {n : ℕ} (w z : Words n Bool) (h : countH w = countH z) : Equiv.Perm (Fin n) :=
  Equiv.ofFiberEquiv (f := w) (g := z) fun b => Fintype.equivOfCardEq (by
    cases b
    · rw [fiber_false_card, fiber_false_card, h]
    · rw [fiber_true_card, fiber_true_card, h])

theorem matchingPerm_map {n : ℕ} (w z : Words n Bool) (h : countH w = countH z) (i : Fin n) :
    z (matchingPerm w z h i) = w i :=
  Equiv.ofFiberEquiv_map (f := w) (g := z) _ i

def wordReindex {n : ℕ} (e : Equiv.Perm (Fin n)) : Words n Bool ≃ Words n Bool where
  toFun w := w ∘ e
  invFun w := w ∘ e.symm
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

theorem countH_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Words n Bool) :
    countH (w ∘ e) = countH w := by
  simp only [countH, hSupport, Finset.card_filter]
  exact Equiv.sum_comp e (fun i => if w i = true then (1 : ℕ) else 0)

theorem wordTensor_reindex (A : Matrix Bool Bool ℂ) (n : ℕ) (e : Equiv.Perm (Fin n))
    (w z : Words n Bool) : wordTensor A n (w ∘ e) (z ∘ e) = wordTensor A n w z := by
  exact Equiv.prod_comp e (fun i => A (w i) (z i))

theorem occupation_reindex (n : ℕ) (e : Equiv.Perm (Fin n))
    (w : Words n Bool) (h : Fin (n + 1)) : occupation n (w ∘ e) h = occupation n w h := by
  simp only [occupation, countH_reindex]

theorem word_action_same_count (A : Matrix Bool Bool ℂ) (n : ℕ)
    (w z : Words n Bool) (h : countH w = countH z) (k : Fin (n + 1)) :
    (wordTensor A n * occupation n) w k = (wordTensor A n * occupation n) z k := by
  let e := matchingPerm w z h
  have hw : w = z ∘ e := by funext i; exact (matchingPerm_map w z h i).symm
  rw [hw]
  change (∑ v : Words n Bool, wordTensor A n (z ∘ e) v * occupation n v k) =
    ∑ v : Words n Bool, wordTensor A n z v * occupation n v k
  calc
    _ = ∑ v : Words n Bool, wordTensor A n (z ∘ e) (v ∘ e) * occupation n (v ∘ e) k :=
      (wordReindex e).sum_comp _ |>.symm
    _ = _ := by simp only [wordTensor_reindex, occupation_reindex]

@[simp] theorem occupationCoeff_conj (n : ℕ) (h : Fin (n + 1)) :
    starRingEnd ℂ (occupationCoeff n h) = occupationCoeff n h := by
  simp [occupationCoeff]

theorem occupation_real (n : ℕ) : (occupation n)ᴴ = (occupation n)ᵀ := by
  ext h w
  by_cases hw : countH w = h.val <;>
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, occupation, hw]

theorem occupation_projection {n : ℕ} (x : Words n Bool → ℂ)
    (hx : ∀ w z, countH w = countH z → x w = x z) :
    occupation n *ᵥ ((occupation n)ᴴ *ᵥ x) = x := by
  funext w
  let cw : Fin (n + 1) := ⟨countH w, Nat.lt_succ_of_le (countH_le w)⟩
  have hcw : cw.val = countH w := rfl
  change (∑ h : Fin (n + 1), occupation n w h * ((occupation n)ᴴ *ᵥ x) h) = x w
  calc
    _ = occupationCoeff n cw * ∑ z : Words n Bool, star (occupation n z cw) * x z := by
      rw [Finset.sum_eq_single cw]
      · simp only [occupation, hcw, if_true, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
      · intro h _ hne
        have hh : countH w ≠ h.val := fun he => hne (Fin.ext (he.symm.trans hcw.symm))
        simp only [occupation, if_neg hh, zero_mul]
      · simp
    _ = occupationCoeff n cw *
        ((∑ z : Words n Bool, if countH z = cw.val then (1 : ℂ) else 0) *
          (occupationCoeff n cw * x w)) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : countH z = cw.val
      · have hxz : x z = x w := hx z w (hz.trans hcw)
        simp [occupation, hz, hxz, -Complex.star_def]
      · simp [occupation, hz]
    _ = (n.choose cw.val : ℂ) * occupationCoeff n cw ^ 2 * x w := by
      rw [fiber_sum]
      ring
    _ = x w := by rw [occupationCoeff_norm]; simp

def symmetricPower (A : Matrix Bool Bool ℂ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (occupation n)ᴴ * wordTensor A n * occupation n

theorem occupation_intertwines (A : Matrix Bool Bool ℂ) (n : ℕ) :
    occupation n * symmetricPower A n = wordTensor A n * occupation n := by
  ext w h
  have hp := congrFun (occupation_projection
    (fun z => (wordTensor A n * occupation n) z h)
    (fun z v hcount => word_action_same_count A n z v hcount h)) w
  simpa only [symmetricPower, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply] using hp

theorem symmetricPower_mul (A B : Matrix Bool Bool ℂ) (n : ℕ) :
    symmetricPower (A * B) n = symmetricPower A n * symmetricPower B n := by
  symm
  calc
    _ = (occupation n)ᴴ * wordTensor A n * (occupation n * symmetricPower B n) := by
      simp only [symmetricPower, Matrix.mul_assoc]
    _ = (occupation n)ᴴ * wordTensor A n * (wordTensor B n * occupation n) := by
      rw [occupation_intertwines]
    _ = symmetricPower (A * B) n := by
      simp only [symmetricPower, wordTensor_mul, Matrix.mul_assoc]

theorem symmetricPower_one (n : ℕ) : symmetricPower (1 : Matrix Bool Bool ℂ) n = 1 := by
  simp only [symmetricPower, wordTensor_one, Matrix.mul_one, occupation_isometry]

theorem wordTensor_transpose (A : Matrix Bool Bool ℂ) (n : ℕ) :
    wordTensor Aᵀ n = (wordTensor A n)ᵀ := rfl

theorem symmetricPower_transpose (A : Matrix Bool Bool ℂ) (n : ℕ) :
    symmetricPower Aᵀ n = (symmetricPower A n)ᵀ := by
  simp only [symmetricPower, wordTensor_transpose, occupation_real, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem symmetricPower_conjTranspose (A : Matrix Bool Bool ℂ) (n : ℕ) :
    symmetricPower Aᴴ n = (symmetricPower A n)ᴴ := by
  simp only [symmetricPower, wordTensor_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

def wordWeight (q : Bool → ℂ) {n : ℕ} (w : Words n Bool) : ℂ := ∏ i : Fin n, q (w i)

theorem wordWeight_count (q : Bool → ℂ) {n : ℕ} (w : Words n Bool) :
    wordWeight q w = q true ^ countH w * q false ^ (n - countH w) := by
  have hp : (∏ i : Fin n, q (w i)) = ∏ i : Fin n, if w i = true then q true else q false := by
    apply Finset.prod_congr rfl
    intro i _
    cases w i <;> simp
  have hc : (Finset.univ.filter fun i : Fin n => ¬w i = true) = (hSupport w)ᶜ := by
    ext i
    simp [hSupport]
  rw [wordWeight, hp, Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hc, Finset.card_compl, Fintype.card_fin]
  rfl

theorem wordTensor_diagonal (q : Bool → ℂ) (n : ℕ) :
    wordTensor (diagonal q) n = diagonal (wordWeight q) := by
  ext w z
  by_cases hwz : w = z
  · subst z
    simp [wordTensor, wordWeight]
  · have hi : ∃ i, w i ≠ z i := by
      by_contra h
      apply hwz
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    have hz : (∏ j : Fin n, diagonal q (w j) (z j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simpa [wordTensor, Matrix.diagonal_apply, hwz] using hz

def occupationWeight (q : Bool → ℂ) (n : ℕ) (h : Fin (n + 1)) : ℂ :=
  q true ^ h.val * q false ^ (n - h.val)

theorem diagonal_intertwines (q : Bool → ℂ) (n : ℕ) :
    wordTensor (diagonal q) n * occupation n = occupation n * diagonal (occupationWeight q n) := by
  rw [wordTensor_diagonal]
  ext w h
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, wordWeight_count]
  by_cases hh : countH w = h.val
  · simp only [occupation, hh, if_true, occupationWeight]
    ring
  · simp only [occupation, if_neg hh, mul_zero, zero_mul]

theorem symmetricPower_diagonal (q : Bool → ℂ) (n : ℕ) :
    symmetricPower (diagonal q) n = diagonal (occupationWeight q n) := by
  rw [symmetricPower, Matrix.mul_assoc, diagonal_intertwines, ← Matrix.mul_assoc,
    occupation_isometry, Matrix.one_mul]

def symmetricTrace (A : Matrix Bool Bool ℂ) (n : ℕ) : ℂ := Matrix.trace (symmetricPower A n)

theorem symmetricTrace_zero (A : Matrix Bool Bool ℂ) : symmetricTrace A 0 = 1 := by
  simp [symmetricTrace, symmetricPower, wordTensor_zero, occupation_isometry]

def singleWordEquiv : Words 1 Bool ≃ Bool where
  toFun w := w 0
  invFun b := fun _ => b
  left_inv w := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
  right_inv b := rfl

theorem sum_words_one (f : Words 1 Bool → ℂ) :
    (∑ w, f w) = f (fun _ => true) + f (fun _ => false) := by
  calc
    _ = ∑ b : Bool, f (singleWordEquiv.symm b) :=
      Fintype.sum_equiv singleWordEquiv _ _ (fun w => by simp)
    _ = _ := by simp [singleWordEquiv]

theorem countH_single_const (b : Bool) :
    countH (fun _ : Fin 1 => b) = if b then 1 else 0 := by
  cases b <;> simp [countH, hSupport]

def singlePolarization (h : Fin 2) : Bool := decide (h.val = 1)

theorem symmetricPower_one_apply (A : Matrix Bool Bool ℂ) (h k : Fin 2) :
    symmetricPower A 1 h k = A (singlePolarization h) (singlePolarization k) := by
  fin_cases h <;> fin_cases k <;>
    simp [symmetricPower, Matrix.mul_apply, Matrix.conjTranspose_apply, sum_words_one,
      occupation, countH_single_const, occupationCoeff, wordTensor,
      singlePolarization]

theorem symmetricTrace_one (A : Matrix Bool Bool ℂ) : symmetricTrace A 1 = Matrix.trace A := by
  simp [symmetricTrace, Matrix.trace, symmetricPower_one_apply, Fin.sum_univ_succ,
    singlePolarization]
  ring

def pairDiagonal (s : RawKernel) (p : Bool) : ℂ :=
  if p then (Real.sqrt s.tH : ℂ) else s.phase * (Real.sqrt s.tV : ℂ)

def pairMatrix (s : RawKernel) : Matrix Bool Bool ℂ := diagonal (pairDiagonal s)

def sourceRoot (s : RawKernel) : ℂ :=
  (Real.sqrt (1 - s.tH) : ℂ) * (Real.sqrt (1 - s.tV) : ℂ)

def sourceZ (s : RawKernel) : ℂ := ((1 - s.tH) * (1 - s.tV) : ℝ)

theorem sourceRoot_norm (s : RawKernel) : star (sourceRoot s) * sourceRoot s = sourceZ s := by
  dsimp only [sourceRoot, sourceZ]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  have hH := Real.mul_self_sqrt (sub_nonneg.mpr s.tH_lt_one.le)
  have hV := Real.mul_self_sqrt (sub_nonneg.mpr s.tV_lt_one.le)
  norm_cast
  linear_combination (Real.sqrt (1 - s.tV)) ^ 2 * hH + (1 - s.tH) * hV

theorem sectorVector_factored (s : RawKernel) (n : ℕ) (h : Fin (n + 1)) :
    sectorVector s n h = sourceRoot s * occupationWeight (pairDiagonal s) n h := by
  simp [sectorVector, amplitude, sourceRoot, occupationWeight, pairDiagonal, mul_pow]
  ring

theorem source_diagonal (s : RawKernel) (n : ℕ) :
    diagonal (sectorVector s n) = sourceRoot s • symmetricPower (pairMatrix s) n := by
  rw [pairMatrix, symmetricPower_diagonal]
  ext h k
  by_cases hh : h = k
  · subst k
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    exact sectorVector_factored s n h
  · simp [hh]

theorem source_star_diagonal (s : RawKernel) (n : ℕ) :
    diagonal (star (sectorVector s n)) =
      star (sourceRoot s) • (symmetricPower (pairMatrix s) n)ᴴ := by
  rw [← Matrix.diagonal_conjTranspose, source_diagonal, Matrix.conjTranspose_smul]

def pairedFinitePhi {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) : ℂ := star v ⬝ᵥ (pairedBlock A B *ᵥ v)

theorem pairedFinitePhi_trace {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) :
    pairedFinitePhi A B v = Matrix.trace (diagonal (star v) * A * diagonal v * Bᵀ) := by
  have hd : ∀ h k, (diagonal (star v) * A * diagonal v) h k = star (v h) * A h k * v k := by
    intro h k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  change (∑ h, star (v h) * ∑ k, pairedBlock A B h k * v k) =
    ∑ h, ∑ k, (diagonal (star v) * A * diagonal v) h k * Bᵀ k h
  simp only [Finset.mul_sum, hd, Matrix.transpose_apply, pairedBlock_apply]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem paired_sector_trace (s : RawKernel) (XA XB : Matrix Bool Bool ℂ) (n : ℕ) :
    pairedFinitePhi (symmetricPower XA n) (symmetricPower XB n) (sectorVector s n) =
      sourceZ s * symmetricTrace ((pairMatrix s)ᴴ * XA * pairMatrix s * XBᵀ) n := by
  rw [pairedFinitePhi_trace, source_star_diagonal, source_diagonal]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [← sourceRoot_norm]
  have hprod : (symmetricPower (pairMatrix s) n)ᴴ * symmetricPower XA n *
      symmetricPower (pairMatrix s) n * (symmetricPower XB n)ᵀ =
      symmetricPower ((pairMatrix s)ᴴ * XA * pairMatrix s * XBᵀ) n := by
    simp only [symmetricPower_mul, symmetricPower_transpose, symmetricPower_conjTranspose]
  rw [hprod]
  dsimp only [symmetricTrace]
  ring

end
end P23.EnvironmentSource.Sector
