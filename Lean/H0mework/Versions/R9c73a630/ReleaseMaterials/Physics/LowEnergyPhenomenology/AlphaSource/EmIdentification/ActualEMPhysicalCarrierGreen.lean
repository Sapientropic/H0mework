import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierSymbol

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMPhysicalCarrier
open SaturationMonoid.PhysicsCore SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair
open scoped BigOperators Matrix

def gaussColorDiagonal (k : Fin 3 → ℝ) : ℝ := gaussSquare k+2*gaugeScale^2
def gaussColorDenominator (k : Fin 3 → ℝ) : ℝ := (gaussSquare k)^2+4*gaugeScale^4

def gaussColorCross (k : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -(k 2:ℂ), (k 1:ℂ); (k 2:ℂ), 0, -(k 0:ℂ); -(k 1:ℂ), (k 0:ℂ), 0]

def gaussColorBlock (k : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (gaussColorDiagonal k:ℂ) • 1 + (2*Complex.I*(gaugeScale:ℂ)) • gaussColorCross k

def gaussColorGreen (k : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (gaussColorDenominator k:ℂ)⁻¹ •
    ((gaussColorDiagonal k:ℂ) • 1 - (2*Complex.I*(gaugeScale:ℂ)) • gaussColorCross k -
      (4*(gaugeScale:ℂ)^2/(gaussColorDiagonal k:ℂ)) •
        Matrix.vecMulVec (fun i => (k i:ℂ)) (fun i => (k i:ℂ)))

theorem gauss_color_diagonal_positive (k : Fin 3 → ℝ) : 0 < gaussColorDiagonal k := by
  have q : 0 ≤ gaussSquare k := Finset.sum_nonneg fun i _ => sq_nonneg (k i)
  have g : 0 < gaugeScale^2 := sq_pos_of_pos gaugeScale_pos
  unfold gaussColorDiagonal
  positivity

theorem gauss_color_denominator_positive (k : Fin 3 → ℝ) : 0 < gaussColorDenominator k := by
  unfold gaussColorDenominator
  have hg := gaugeScale_pos
  positivity

private theorem cross_square (k : Fin 3 → ℝ) :
    gaussColorCross k*gaussColorCross k =
      Matrix.vecMulVec (fun i => (k i:ℂ)) (fun i => (k i:ℂ)) - (gaussSquare k:ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
  · change 0*0 + (-(k 2:ℂ))*(k 2:ℂ) + (k 1:ℂ)*(-(k 1:ℂ)) = (k 0:ℂ)*(k 0:ℂ)-(gaussSquare k:ℂ)*1
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change 0*(-(k 2:ℂ)) + (-(k 2:ℂ))*0 + (k 1:ℂ)*(k 0:ℂ) = (k 0:ℂ)*(k 1:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change 0*(k 1:ℂ) + (-(k 2:ℂ))*(-(k 0:ℂ)) + (k 1:ℂ)*0 = (k 0:ℂ)*(k 2:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (k 2:ℂ)*0 + 0*(k 2:ℂ) + (-(k 0:ℂ))*(-(k 1:ℂ)) = (k 1:ℂ)*(k 0:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (k 2:ℂ)*(-(k 2:ℂ)) + 0*0 + (-(k 0:ℂ))*(k 0:ℂ) = (k 1:ℂ)*(k 1:ℂ)-(gaussSquare k:ℂ)*1
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (k 2:ℂ)*(k 1:ℂ) + 0*(-(k 0:ℂ)) + (-(k 0:ℂ))*0 = (k 1:ℂ)*(k 2:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (-(k 1:ℂ))*0 + (k 0:ℂ)*(k 2:ℂ) + 0*(-(k 1:ℂ)) = (k 2:ℂ)*(k 0:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (-(k 1:ℂ))*(-(k 2:ℂ)) + (k 0:ℂ)*0 + 0*(k 0:ℂ) = (k 2:ℂ)*(k 1:ℂ)-(gaussSquare k:ℂ)*0
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  · change (-(k 1:ℂ))*(k 1:ℂ) + (k 0:ℂ)*(-(k 0:ℂ)) + 0*0 = (k 2:ℂ)*(k 2:ℂ)-(gaussSquare k:ℂ)*1
    simp only [gaussSquare, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_pow]
    ring

private theorem cross_outer (k : Fin 3 → ℝ) :
    gaussColorCross k*Matrix.vecMulVec (fun i => (k i:ℂ)) (fun i => (k i:ℂ)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
  · change 0*((k 0:ℂ)*(k 0:ℂ)) + (-(k 2:ℂ))*((k 1:ℂ)*(k 0:ℂ)) + (k 1:ℂ)*((k 2:ℂ)*(k 0:ℂ)) = 0
    ring
  · change 0*((k 0:ℂ)*(k 1:ℂ)) + (-(k 2:ℂ))*((k 1:ℂ)*(k 1:ℂ)) + (k 1:ℂ)*((k 2:ℂ)*(k 1:ℂ)) = 0
    ring
  · change 0*((k 0:ℂ)*(k 2:ℂ)) + (-(k 2:ℂ))*((k 1:ℂ)*(k 2:ℂ)) + (k 1:ℂ)*((k 2:ℂ)*(k 2:ℂ)) = 0
    ring
  · change (k 2:ℂ)*((k 0:ℂ)*(k 0:ℂ)) + 0*((k 1:ℂ)*(k 0:ℂ)) + (-(k 0:ℂ))*((k 2:ℂ)*(k 0:ℂ)) = 0
    ring
  · change (k 2:ℂ)*((k 0:ℂ)*(k 1:ℂ)) + 0*((k 1:ℂ)*(k 1:ℂ)) + (-(k 0:ℂ))*((k 2:ℂ)*(k 1:ℂ)) = 0
    ring
  · change (k 2:ℂ)*((k 0:ℂ)*(k 2:ℂ)) + 0*((k 1:ℂ)*(k 2:ℂ)) + (-(k 0:ℂ))*((k 2:ℂ)*(k 2:ℂ)) = 0
    ring
  · change (-(k 1:ℂ))*((k 0:ℂ)*(k 0:ℂ)) + (k 0:ℂ)*((k 1:ℂ)*(k 0:ℂ)) + 0*((k 2:ℂ)*(k 0:ℂ)) = 0
    ring
  · change (-(k 1:ℂ))*((k 0:ℂ)*(k 1:ℂ)) + (k 0:ℂ)*((k 1:ℂ)*(k 1:ℂ)) + 0*((k 2:ℂ)*(k 1:ℂ)) = 0
    ring
  · change (-(k 1:ℂ))*((k 0:ℂ)*(k 2:ℂ)) + (k 0:ℂ)*((k 1:ℂ)*(k 2:ℂ)) + 0*((k 2:ℂ)*(k 2:ℂ)) = 0
    ring

/-- The complete color block is inverted at every momentum, including zero. -/
theorem gauss_color_green_inverse (k : Fin 3 → ℝ) :
    gaussColorBlock k * gaussColorGreen k = 1 ∧ gaussColorGreen k * gaussColorBlock k = 1 := by
  have ha : (gaussColorDiagonal k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gauss_color_diagonal_positive k).ne'
  have hd : (gaussColorDenominator k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gauss_color_denominator_positive k).ne'
  let a : ℂ := gaussColorDiagonal k
  let b : ℂ := 2*Complex.I*(gaugeScale:ℂ)
  let c : ℂ := 4*(gaugeScale:ℂ)^2/a
  let q : ℂ := gaussSquare k
  let d : ℂ := gaussColorDenominator k
  let C := gaussColorCross k
  let P := Matrix.vecMulVec (fun i => (k i:ℂ)) (fun i => (k i:ℂ))
  have square : C*C = P-q • 1 := cross_square k
  have outer : C*P = 0 := cross_outer k
  have numerator : (a • (1 : Matrix (Fin 3) (Fin 3) ℂ)+b • C)*(a • 1-b • C-c • P) =
      (a*a+b*b*q) • 1+(-b*b-a*c) • P := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, square, outer, smul_zero, smul_sub, smul_smul]
    module
  have hb : b*b = -4*(gaugeScale:ℂ)^2 := by
    dsimp [b]
    calc
      _ = 4*(gaugeScale:ℂ)^2*Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hc : a*c = 4*(gaugeScale:ℂ)^2 := by
    dsimp [c]
    field_simp [show a ≠ 0 from ha]
  have had : a*a-4*(gaugeScale:ℂ)^2*q = d := by
    dsimp [a, q, d, gaussColorDiagonal, gaussColorDenominator]
    push_cast
    ring
  rw [hb, hc] at numerator
  have coefficients : a*a+(-4*(gaugeScale:ℂ)^2)*q = d := by linear_combination had
  rw [coefficients] at numerator
  have coefficient_zero : -b*b-4*(gaugeScale:ℂ)^2 = 0 := by linear_combination -hb
  rw [coefficient_zero, zero_smul, add_zero] at numerator
  have left : gaussColorBlock k*gaussColorGreen k = 1 := by
    change (a • 1+b • C)*(d⁻¹ • (a • 1-b • C-c • P)) = 1
    rw [Matrix.mul_smul, numerator, smul_smul, inv_mul_cancel₀ hd, one_smul]
  exact ⟨left, mul_eq_one_comm.mp left⟩

/-- The fourth component is the original hypercharge direction; no EM relabelling is made. -/
def gaussFullBlock (k : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (gaussColorBlock k) 0 0 ((gaussSquare k:ℂ) • 1)

def gaussFullGreen (k : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (gaussColorGreen k) 0 0 ((gaussSquare k:ℂ)⁻¹ • 1)

theorem gauss_full_green_inverse (k : Fin 3 → ℝ) (hk : gaussSquare k ≠ 0) :
    gaussFullBlock k * gaussFullGreen k = 1 ∧ gaussFullGreen k * gaussFullBlock k = 1 := by
  have hkc : (gaussSquare k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have lower : ((gaussSquare k:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
      ((gaussSquare k:ℂ)⁻¹ • 1) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hkc]
  have left : gaussFullBlock k * gaussFullGreen k = 1 := by
    rw [gaussFullBlock, gaussFullGreen, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      (gauss_color_green_inverse k).1, lower, Matrix.fromBlocks_one]
  exact ⟨left, mul_eq_one_comm.mp left⟩

def gaussCurrentMetric : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => 1/2) (fun _ => 1))

def gaussCurrentMetricInverse : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => 2) (fun _ => 1))

def gaussCurrentGreen (k : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  -((2*lapse:ℝ):ℂ)⁻¹ • (gaussFullGreen k*gaussCurrentMetricInverse)

/-- The original 2*lapse flux and the non-unit color pairing are retained on both sides. -/
theorem gauss_current_green_equation (k : Fin 3 → ℝ) (hk : gaussSquare k ≠ 0) :
    (((2*lapse:ℝ):ℂ) • (gaussCurrentMetric*gaussFullBlock k))*gaussCurrentGreen k = -1 := by
  have hm : gaussCurrentMetric*gaussCurrentMetricInverse = 1 := by
    rw [gaussCurrentMetric, gaussCurrentMetricInverse, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i =>
      (Sum.elim (fun _ : Fin 3 => (1/2:ℂ)) (fun _ : Fin 1 => 1) i)*
      (Sum.elim (fun _ : Fin 3 => (2:ℂ)) (fun _ : Fin 1 => 1) i)) = Matrix.diagonal (fun _ => 1)
    congr 1
    funext i
    cases i <;> norm_num

  have hl : ((2*lapse:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) lapse_pos.ne')
  rw [gaussCurrentGreen, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have matrix : gaussCurrentMetric*gaussFullBlock k*(gaussFullGreen k*gaussCurrentMetricInverse) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gaussFullBlock k), (gauss_full_green_inverse k hk).1,
      Matrix.one_mul, hm]
  rw [matrix]
  have scale : ((2*lapse:ℝ):ℂ)*(-((2*lapse:ℝ):ℂ)⁻¹) = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hl]
  rw [scale]
  simp

end LowEnergy.GaussComposite.ActualEMPhysicalCarrier
