import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.NativeEffects.Detectorgamma

set_option autoImplicit false

namespace P23.EnvironmentSource

open Matrix
open P23.GaussianWindow.NativeEffects
open scoped BigOperators ComplexOrder
noncomputable section

structure EnvironmentPrim where
  detector : DetectorPrim
  xi : ℂ
  xi_bound : Complex.normSq xi ≤ 1

def environmentComplement (s : EnvironmentPrim) : ℂ :=
  ((Real.sqrt (1 - Complex.normSq s.xi)) : ℝ)

def hRoot (s : EnvironmentPrim) : ℂ := ((Real.sqrt s.detector.TH) : ℝ)
def vRoot (s : EnvironmentPrim) : ℂ := ((Real.sqrt s.detector.TV) : ℝ)
def hLost (s : EnvironmentPrim) : ℂ := ((Real.sqrt (1 - s.detector.TH)) : ℝ)
def vLost (s : EnvironmentPrim) : ℂ := ((Real.sqrt (1 - s.detector.TV)) : ℝ)

@[simp] theorem star_environmentComplement (s : EnvironmentPrim) :
    star (environmentComplement s) = environmentComplement s := by
  simp [environmentComplement]

@[simp] theorem star_hRoot (s : EnvironmentPrim) : star (hRoot s) = hRoot s := by
  simp [hRoot]

@[simp] theorem star_vRoot (s : EnvironmentPrim) : star (vRoot s) = vRoot s := by
  simp [vRoot]

@[simp] theorem star_hLost (s : EnvironmentPrim) : star (hLost s) = hLost s := by
  simp [hLost]

@[simp] theorem star_vLost (s : EnvironmentPrim) : star (vLost s) = vLost s := by
  simp [vLost]

@[simp] theorem conj_environmentComplement (s : EnvironmentPrim) :
    starRingEnd ℂ (environmentComplement s) = environmentComplement s := by
  simp [environmentComplement]

@[simp] theorem conj_hRoot (s : EnvironmentPrim) : starRingEnd ℂ (hRoot s) = hRoot s := by
  simp [hRoot]

@[simp] theorem conj_vRoot (s : EnvironmentPrim) : starRingEnd ℂ (vRoot s) = vRoot s := by
  simp [vRoot]

@[simp] theorem conj_hLost (s : EnvironmentPrim) : starRingEnd ℂ (hLost s) = hLost s := by
  simp [hLost]

@[simp] theorem conj_vLost (s : EnvironmentPrim) : starRingEnd ℂ (vLost s) = vLost s := by
  simp [vLost]

theorem hRoot_sq (s : EnvironmentPrim) : hRoot s ^ 2 = (s.detector.TH : ℂ) := by
  dsimp only [hRoot]
  exact_mod_cast Real.sq_sqrt s.detector.TH_nonneg

theorem vRoot_sq (s : EnvironmentPrim) : vRoot s ^ 2 = (s.detector.TV : ℂ) := by
  dsimp only [vRoot]
  exact_mod_cast Real.sq_sqrt s.detector.TV_nonneg

theorem hLost_sq (s : EnvironmentPrim) : hLost s ^ 2 = 1 - (s.detector.TH : ℂ) := by
  dsimp only [hLost]
  exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr s.detector.TH_le_one)

theorem vLost_sq (s : EnvironmentPrim) : vLost s ^ 2 = 1 - (s.detector.TV : ℂ) := by
  dsimp only [vLost]
  exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr s.detector.TV_le_one)

theorem xi_norm (s : EnvironmentPrim) : star s.xi * s.xi = (Complex.normSq s.xi : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm

theorem environment_unit (s : EnvironmentPrim) :
    star s.xi * s.xi + environmentComplement s ^ 2 = 1 := by
  rw [xi_norm]
  have hs : environmentComplement s ^ 2 = 1 - (Complex.normSq s.xi : ℂ) := by
    dsimp only [environmentComplement]
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr s.xi_bound)
  rw [hs]
  ring

def environmentColumn (s : EnvironmentPrim) (p u : Bool) : ℂ :=
  if p then (if u then 1 else 0)
  else (if u then s.xi else environmentComplement s)

def occupiedColumns (s : EnvironmentPrim) : Matrix (Bool × Bool) Bool ℂ :=
  fun pu p => if pu.1 = p then environmentColumn s p pu.2 else 0

theorem occupiedColumns_isometry (s : EnvironmentPrim) :
    (occupiedColumns s)ᴴ * occupiedColumns s = 1 := by
  ext i j
  change (∑ pu : Bool × Bool, star (occupiedColumns s pu i) * occupiedColumns s pu j) =
    if i = j then 1 else 0
  cases i <;> cases j <;>
    simp [occupiedColumns, environmentColumn, Fintype.sum_prod_type,
      -Complex.star_def]
  simpa only [pow_two, Complex.star_def] using environment_unit s

def clickedRows (s : EnvironmentPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  fun u p => if u then
    (if p then hRoot s * (Real.sin a : ℂ) else vRoot s * s.xi * (Real.cos a : ℂ))
  else (if p then 0 else vRoot s * environmentComplement s * (Real.cos a : ℂ))

def transmittedColumns (s : EnvironmentPrim) : Matrix (Bool × Bool) Bool ℂ :=
  fun pu p => occupiedColumns s pu p * (if p then hRoot s else vRoot s)

def analyzerRows (a : ℝ) : Matrix Bool (Bool × Bool) ℂ :=
  fun u pv => if u = pv.2 then analyzerVector a pv.1 else 0

def clockwiseRotation (delta : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then (Real.cos delta : ℂ) else (Real.sin delta : ℂ))
    else (if j then -(Real.sin delta : ℂ) else (Real.cos delta : ℂ))

def polarizationAction (delta : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun pu qv => if pu.2 = qv.2 then clockwiseRotation delta pu.1 qv.1 else 0

def physicalClickedRows (s : EnvironmentPrim) (a delta : ℝ) : Matrix Bool Bool ℂ :=
  analyzerRows a * polarizationAction delta * transmittedColumns s

theorem clickedRows_from_source (s : EnvironmentPrim) (a : ℝ) :
    analyzerRows a * transmittedColumns s = clickedRows s a := by
  ext u p
  change (∑ pv : Bool × Bool, analyzerRows a u pv * transmittedColumns s pv p) =
    clickedRows s a u p
  cases u <;> cases p <;>
    simp [analyzerRows, transmittedColumns, occupiedColumns, environmentColumn, clickedRows,
      analyzerVector, Fintype.sum_prod_type,
      -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.star_def] <;> ring

theorem analyzer_rotation (a delta : ℝ) :
    analyzerRows a * polarizationAction delta = analyzerRows (a - delta) := by
  ext u pv
  rcases pv with ⟨p, v⟩
  change (∑ qw : Bool × Bool, analyzerRows a u qw * polarizationAction delta qw (p, v)) =
    analyzerRows (a - delta) u (p, v)
  cases u <;> cases p <;> cases v <;>
    simp [analyzerRows, polarizationAction, clockwiseRotation, analyzerVector,
      Fintype.sum_prod_type, Real.sin_sub, Real.cos_sub,
      -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.star_def] <;> ring

theorem physicalClickedRows_generated (s : EnvironmentPrim) (a delta : ℝ) :
    physicalClickedRows s a delta = clickedRows s (a - delta) := by
  rw [physicalClickedRows, analyzer_rotation, clickedRows_from_source]

def perpendicularRows (s : EnvironmentPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  fun u p => if u then
    (if p then hRoot s * (Real.cos a : ℂ) else -(vRoot s * s.xi * (Real.sin a : ℂ)))
  else (if p then 0 else -(vRoot s * environmentComplement s * (Real.sin a : ℂ)))

def lostRows (s : EnvironmentPrim) : Matrix Bool Bool ℂ :=
  fun u p => if u then (if p then hLost s else 0) else (if p then 0 else vLost s)

def sixPorts (s : EnvironmentPrim) (a : ℝ) : Matrix (Fin 6) Bool ℂ :=
  ![clickedRows s a true, clickedRows s a false,
    perpendicularRows s a true, perpendicularRows s a false,
    lostRows s true, lostRows s false]

def noClickRows (s : EnvironmentPrim) (a : ℝ) : Matrix (Fin 4) Bool ℂ :=
  ![perpendicularRows s a true, perpendicularRows s a false,
    lostRows s true, lostRows s false]

def clickedGram (s : EnvironmentPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  (clickedRows s a)ᴴ * clickedRows s a

def noClickGram (s : EnvironmentPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  (noClickRows s a)ᴴ * noClickRows s a

theorem sixPorts_gram (s : EnvironmentPrim) (a : ℝ) : (sixPorts s a)ᴴ * sixPorts s a = 1 := by
  have hH := hRoot_sq s
  have hV := vRoot_sq s
  have hLH := hLost_sq s
  have hLV := vLost_sq s
  have henv := environment_unit s
  simp only [Complex.star_def] at henv
  have hu : (Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq a
  ext i j
  change (∑ k : Fin 6, star (sixPorts s a k i) * sixPorts s a k j) =
    if i = j then 1 else 0
  cases i <;> cases j <;>
    simp [sixPorts, clickedRows, perpendicularRows, lostRows, Fin.sum_univ_succ,
      -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.star_def]
  case false.false =>
    linear_combination vRoot s ^ 2 * ((Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2) * henv +
      vRoot s ^ 2 * hu + hV + hLV
  case false.true => ring
  case true.false => ring
  case true.true => linear_combination hRoot s ^ 2 * hu + hH + hLH

theorem sixPorts_gram_split (s : EnvironmentPrim) (a : ℝ) :
    (sixPorts s a)ᴴ * sixPorts s a = clickedGram s a + noClickGram s a := by
  ext i j
  change (∑ k : Fin 6, star (sixPorts s a k i) * sixPorts s a k j) =
    (∑ u : Bool, star (clickedRows s a u i) * clickedRows s a u j) +
      ∑ k : Fin 4, star (noClickRows s a k i) * noClickRows s a k j
  simp [sixPorts, noClickRows, Fin.sum_univ_succ]
  ring

theorem click_noClick_sum (s : EnvironmentPrim) (a : ℝ) :
    clickedGram s a + noClickGram s a = 1 := by
  rw [← sixPorts_gram_split, sixPorts_gram]

theorem noClick_complement (s : EnvironmentPrim) (a : ℝ) :
    noClickGram s a = 1 - clickedGram s a := by
  rw [← click_noClick_sum s a]
  abel

theorem click_complement (s : EnvironmentPrim) (a : ℝ) :
    1 - noClickGram s a = clickedGram s a := by
  rw [noClick_complement]
  abel

theorem onePhoton_bounds (s : EnvironmentPrim) (a : ℝ) :
    (noClickGram s a).PosSemidef ∧ (1 - noClickGram s a).PosSemidef := by
  refine ⟨posSemidef_conjTranspose_mul_self (noClickRows s a), ?_⟩
  rw [click_complement]
  exact posSemidef_conjTranspose_mul_self (clickedRows s a)

def clickedFormula (s : EnvironmentPrim) (a : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => if i then
    (if j then (s.detector.TH : ℂ) * (Real.sin a : ℂ) ^ 2
      else hRoot s * vRoot s * (Real.sin a : ℂ) * (Real.cos a : ℂ) * s.xi)
  else
    (if j then hRoot s * vRoot s * (Real.sin a : ℂ) * (Real.cos a : ℂ) * star s.xi
      else (s.detector.TV : ℂ) * (Real.cos a : ℂ) ^ 2)

theorem clickedGram_formula (s : EnvironmentPrim) (a : ℝ) :
    clickedGram s a = clickedFormula s a := by
  have hH := hRoot_sq s
  have hV := vRoot_sq s
  have henv := environment_unit s
  simp only [Complex.star_def] at henv
  ext i j
  change (∑ u : Bool, star (clickedRows s a u i) * clickedRows s a u j) = clickedFormula s a i j
  cases i <;> cases j <;>
    simp [clickedRows, clickedFormula,
      -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.star_def]
  case false.false =>
    linear_combination vRoot s ^ 2 * (Real.cos a : ℂ) ^ 2 * henv + (Real.cos a : ℂ) ^ 2 * hV
  case false.true => ring
  case true.false => ring
  case true.true => linear_combination (Real.sin a : ℂ) ^ 2 * hH

def determinantDefect (E : Matrix Bool Bool ℂ) : ℂ :=
  E true true * E false false - E true false * E false true

theorem clickedGram_determinant (s : EnvironmentPrim) (a : ℝ) :
    determinantDefect (clickedGram s a) =
      ((s.detector.TH * s.detector.TV * Real.sin a ^ 2 * Real.cos a ^ 2 *
        (1 - Complex.normSq s.xi)) : ℝ) := by
  rw [clickedGram_formula]
  simp only [determinantDefect, clickedFormula, Bool.false_eq_true,
    if_true, if_false, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_one]
  calc
    _ = (s.detector.TH : ℂ) * (s.detector.TV : ℂ) * (Real.sin a : ℂ) ^ 2 *
          (Real.cos a : ℂ) ^ 2 - hRoot s ^ 2 * vRoot s ^ 2 * (Real.sin a : ℂ) ^ 2 *
          (Real.cos a : ℂ) ^ 2 * (star s.xi * s.xi) := by ring
    _ = _ := by rw [hRoot_sq, vRoot_sq, xi_norm]; ring

theorem outer_determinant_zero (v : Bool → ℂ) :
    determinantDefect (vecMulVec v (star v)) = 0 := by
  change v true * star (v true) * (v false * star (v false)) -
    v true * star (v false) * (v false * star (v true)) = 0
  ring

theorem clickedGram_not_rankOne (s : EnvironmentPrim) (a : ℝ)
    (hH : 0 < s.detector.TH) (hV : 0 < s.detector.TV)
    (hs : Real.sin a ≠ 0) (hc : Real.cos a ≠ 0)
    (hxi : Complex.normSq s.xi < 1) (v : Bool → ℂ) :
    clickedGram s a ≠ vecMulVec v (star v) := by
  intro heq
  have hd := clickedGram_determinant s a
  rw [heq, outer_determinant_zero] at hd
  have hp : 0 < s.detector.TH * s.detector.TV * Real.sin a ^ 2 * Real.cos a ^ 2 *
      (1 - Complex.normSq s.xi) :=
    mul_pos (mul_pos (mul_pos (mul_pos hH hV) (sq_pos_of_ne_zero hs))
      (sq_pos_of_ne_zero hc)) (sub_pos.mpr hxi)
  have hz : s.detector.TH * s.detector.TV * Real.sin a ^ 2 * Real.cos a ^ 2 *
      (1 - Complex.normSq s.xi) = 0 := by exact_mod_cast hd.symm
  exact ne_of_gt hp hz

def gamma (s : EnvironmentPrim) (a : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (occupation n)ᴴ * wordTensor (noClickGram s a) n * occupation n

def numberPorts (s : EnvironmentPrim) (a : ℝ) (n : ℕ) :
    Matrix (Words n (Fin 4)) (Fin (n + 1)) ℂ :=
  wordTensor (noClickRows s a) n * occupation n

theorem gamma_port_born (s : EnvironmentPrim) (a : ℝ) (n : ℕ) :
    gamma s a n = (numberPorts s a n)ᴴ * numberPorts s a n := by
  simp only [gamma, numberPorts, noClickGram, wordTensor_mul, wordTensor_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem allPorts_number_isometry (s : EnvironmentPrim) (a : ℝ) (n : ℕ) :
    (wordTensor (sixPorts s a) n * occupation n)ᴴ *
      (wordTensor (sixPorts s a) n * occupation n) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (wordTensor _ n)ᴴ,
    ← wordTensor_conjTranspose, ← wordTensor_mul, sixPorts_gram, wordTensor_one,
    Matrix.one_mul, occupation_isometry]

theorem gamma_bounds (s : EnvironmentPrim) (a : ℝ) (n : ℕ) :
    (gamma s a n).PosSemidef ∧ (1 - gamma s a n).PosSemidef := by
  have h := wordTensor_bounds (onePhoton_bounds s a).1 (onePhoton_bounds s a).2 n
  refine ⟨h.1.conjTranspose_mul_mul_same (occupation n), ?_⟩
  have heq : (occupation n)ᴴ * (1 - wordTensor (noClickGram s a) n) * occupation n =
      1 - gamma s a n := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, occupation_isometry, gamma]
  rw [← heq]
  exact h.2.conjTranspose_mul_mul_same (occupation n)

theorem rankOne_clicked (s : EnvironmentPrim) (a : ℝ) (hxi : s.xi = 1) :
    clickedGram s a = (clickedPorts s.detector a)ᴴ * clickedPorts s.detector a := by
  ext i j
  change (∑ u : Bool, star (clickedRows s a u i) * clickedRows s a u j) =
    ∑ k : Fin 1, star (clickedPorts s.detector a k i) * clickedPorts s.detector a k j
  cases i <;> cases j <;>
    simp [clickedRows, clickedPorts, clickRow, hRoot, vRoot, environmentComplement, hxi,
      -Complex.ofReal_sin, -Complex.ofReal_cos, -Complex.star_def]

theorem rankOne_noClick (s : EnvironmentPrim) (a : ℝ) (hxi : s.xi = 1) :
    noClickGram s a = onePhotonEffect s.detector a := by
  rw [noClick_complement, rankOne_clicked s a hxi,
    ← P23.GaussianWindow.NativeEffects.onePhoton_complement]
  abel

theorem rankOne_gamma (s : EnvironmentPrim) (a : ℝ) (n : ℕ) (hxi : s.xi = 1) :
    gamma s a n = P23.GaussianWindow.NativeEffects.gamma s.detector a n := by
  simp only [gamma, P23.GaussianWindow.NativeEffects.gamma, rankOne_noClick s a hxi]

end
end P23.EnvironmentSource
