import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Sqrt

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
noncomputable section

def eLow : ℚ := 27182818283 / 10^10

theorem eLow_pos : (0 : ℚ) < eLow := by unfold eLow; norm_num

theorem eLow_lt_e : (eLow : ℝ) < Real.exp 1 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have eq : (eLow : ℝ) = 2.7182818283 := by
    unfold eLow
    norm_num
  rw [eq]
  exact h

def weightScale : ℚ := 2^64
def weightScaleSq : ℚ := 2^128

theorem weightScale_pos : (0 : ℚ) < weightScale := by unfold weightScale; positivity

def gaussMomentTarget (k : ℕ) (beta : ℚ) : ℚ :=
  ((k : ℚ) / (2 * eLow * beta))^k

def gaussMoment (k : ℕ) (beta : ℚ) : ℚ :=
  if k = 0 then 1
  else ((Nat.sqrt (Int.toNat ⌈gaussMomentTarget k beta * weightScaleSq⌉) + 1 : ℚ) /
    weightScale)

theorem gaussMoment_nonneg (k : ℕ) (beta : ℚ) : 0 ≤ gaussMoment k beta := by
  unfold gaussMoment
  split_ifs
  · norm_num
  · exact div_nonneg (by exact_mod_cast Nat.zero_le _) weightScale_pos.le

theorem gaussMoment_sq_ge (k : ℕ) (beta : ℚ) (hbeta : 0 < beta) :
    (gaussMomentTarget k beta : ℝ) ≤ ((gaussMoment k beta : ℝ))^2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [gaussMoment, gaussMomentTarget]
  · have hk' : ¬k = 0 := hk.ne'
    set N : ℕ := Int.toNat ⌈gaussMomentTarget k beta * weightScaleSq⌉
    have tnonneg : (0 : ℚ) ≤ gaussMomentTarget k beta * weightScaleSq := by
      have e0 := eLow_pos
      have bp := hbeta.le
      have w2 : (0 : ℚ) < weightScaleSq := by unfold weightScaleSq; positivity
      unfold gaussMomentTarget
      positivity
    have ceilNonneg : (0 : ℤ) ≤ ⌈gaussMomentTarget k beta * weightScaleSq⌉ :=
      Int.ceil_nonneg tnonneg
    have nCeilQ : (N : ℚ) = ⌈gaussMomentTarget k beta * weightScaleSq⌉ := by
      have h : (N : ℤ) = ⌈gaussMomentTarget k beta * weightScaleSq⌉ :=
        Int.toNat_of_nonneg ceilNonneg
      exact_mod_cast h
    have ceilLe : gaussMomentTarget k beta * weightScaleSq ≤ (N : ℚ) := by
      have h : (N : ℤ) = ⌈gaussMomentTarget k beta * weightScaleSq⌉ :=
        Int.toNat_of_nonneg ceilNonneg
      have hQ : (N : ℚ) = ⌈gaussMomentTarget k beta * weightScaleSq⌉ := by
        exact_mod_cast h
      exact hQ ▸ Int.le_ceil _
    have hsR : (0 : ℝ) < weightScale := by exact_mod_cast weightScale_pos
    have scaleSqR : (weightScaleSq : ℝ) = (weightScale : ℝ)^2 := by
      unfold weightScaleSq weightScale
      norm_num
    have e1 : (gaussMomentTarget k beta : ℝ) =
        (gaussMomentTarget k beta * weightScaleSq : ℝ) / ((weightScale : ℝ)^2) := by
      rw [scaleSqR, mul_div_cancel_right₀ _ (pow_ne_zero 2 hsR.ne')]
    have casted : (gaussMoment k beta : ℝ) = ((Nat.sqrt N : ℝ) + 1) / weightScale := by
      have e : gaussMoment k beta = ((Nat.sqrt N + 1 : ℚ) / weightScale) := by
        unfold gaussMoment
        rw [if_neg hk']
      rw [e]
      push_cast
      rfl
    have h2 : (N : ℝ) ≤ ((Nat.sqrt N : ℝ) + 1)^2 := by
      have h2N : N ≤ (Nat.sqrt N + 1)^2 := by
        rw [pow_two]
        exact (Nat.lt_succ_sqrt N).le
      exact_mod_cast h2N
    rw [e1, casted]
    calc (gaussMomentTarget k beta * weightScaleSq : ℝ) / ((weightScale : ℝ)^2)
        ≤ (N : ℝ) / ((weightScale : ℝ)^2) :=
          div_le_div_of_nonneg_right (by exact_mod_cast ceilLe) (pow_pos hsR 2).le
      _ ≤ (((Nat.sqrt N : ℝ) + 1) / weightScale)^2 := by
          rw [div_pow]
          exact div_le_div_of_nonneg_right h2 (pow_pos hsR 2).le

theorem one_le_exp_sub_one (z : ℝ) : z ≤ Real.exp (z - 1) := by
  have h := Real.add_one_le_exp (z - 1)
  linarith

theorem e_mul_le_exp (z : ℝ) : Real.exp 1 * z ≤ Real.exp z := by
  calc Real.exp 1 * z ≤ Real.exp 1 * Real.exp (z - 1) :=
      mul_le_mul_of_nonneg_left (one_le_exp_sub_one z) (Real.exp_pos _).le
    _ = Real.exp z := by rw [← Real.exp_add]; ring_nf

theorem pow_mul_exp_neg_le (k : ℕ) (y : ℝ) (hk : 0 < k) (hy : 0 ≤ y) :
    y ^ k * Real.exp (-y) ≤ ((k : ℝ) / Real.exp 1) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have step : (Real.exp 1 * (y / k)) ^ k ≤ Real.exp y := by
    calc (Real.exp 1 * (y / k)) ^ k ≤ (Real.exp (y / k)) ^ k :=
        pow_le_pow_left₀ (by positivity) (e_mul_le_exp (y / k)) k
      _ = Real.exp y := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have e1 : (Real.exp 1 * (y / k)) ^ k * (k : ℝ) ^ k = y ^ k * (Real.exp 1) ^ k := by
    rw [mul_pow, div_pow]
    field_simp
  have key : y ^ k * (Real.exp 1) ^ k ≤ (k : ℝ) ^ k * Real.exp y := by
    calc y ^ k * (Real.exp 1) ^ k = (Real.exp 1 * (y / k)) ^ k * (k : ℝ) ^ k := e1.symm
      _ ≤ Real.exp y * (k : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right step (by positivity)
      _ = (k : ℝ) ^ k * Real.exp y := by ring
  have side : y ^ k ≤ (k : ℝ)^k * Real.exp y / (Real.exp 1)^k :=
    (le_div_iff₀ (pow_pos (Real.exp_pos 1) k)).mpr key
  calc y ^ k * Real.exp (-y) ≤
        ((k : ℝ)^k * Real.exp y / (Real.exp 1)^k) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right side (Real.exp_pos _).le
    _ = ((k : ℝ) / Real.exp 1) ^ k := by
        rw [div_pow, div_mul_eq_mul_div, mul_assoc, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, mul_one]

theorem abs_pow_mul_exp_neg_sq_le (k : ℕ) (beta : ℚ) (hbeta : 0 < beta) (u : ℝ) :
    (|u| ^ k * Real.exp (-(beta : ℝ) * u^2))^2 ≤ (gaussMomentTarget k beta : ℝ) := by
  have hβ : (0 : ℝ) < beta := by exact_mod_cast hbeta
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h2 : (gaussMomentTarget 0 beta : ℝ) = 1 := by
      simp [gaussMomentTarget]
    rw [h2]
    have h1 : Real.exp (-(beta : ℝ) * u^2) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (sq_nonneg u))
    nlinarith [Real.exp_pos (-(beta : ℝ) * u^2)]
  · have squared : (|u| ^ k * Real.exp (-(beta : ℝ) * u^2))^2 =
        ((2 * beta * u^2 : ℝ)^k * Real.exp (-(2 * beta * u^2))) / (2 * (beta : ℝ))^k := by
      have e1 : (|u| ^ k)^2 = (u^2)^k := by
        rw [← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs]
      have e2 : (Real.exp (-(beta : ℝ) * u^2))^2 = Real.exp (-(2 * beta * u^2)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have e3 : ((2 * beta * u^2) : ℝ)^k = (2 * beta)^k * (u^2)^k := mul_pow _ _ _
      rw [mul_pow, e1, e2, e3]
      field_simp
    rw [squared]
    have h2β : (0 : ℝ) < 2 * beta := by positivity
    have h2βeLow : (0 : ℝ) < 2 * beta * eLow :=
      mul_pos h2β (by exact_mod_cast eLow_pos)
    have main := pow_mul_exp_neg_le k (2 * beta * u^2) hk
      (mul_nonneg h2β.le (sq_nonneg u))
    calc (2 * beta * u^2 : ℝ)^k * Real.exp (-(2 * beta * u^2)) / (2 * beta)^k
        ≤ ((k : ℝ) / Real.exp 1)^k / (2 * beta)^k :=
          div_le_div_of_nonneg_right main (pow_pos h2β k).le
      _ = ((k : ℝ) / (2 * beta * Real.exp 1))^k := by
          rw [div_pow, div_pow]
          field_simp
          rw [mul_pow]
          ring
      _ ≤ ((k : ℝ) / (2 * beta * eLow))^k := by
          apply pow_le_pow_left₀ _ _ k
          · apply div_nonneg (Nat.cast_nonneg k)
            positivity
          · exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) h2βeLow
              (mul_le_mul_of_nonneg_left (le_of_lt eLow_lt_e) h2β.le)
      _ = (gaussMomentTarget k beta : ℝ) := by
          unfold gaussMomentTarget
          push_cast
          rw [mul_right_comm]

theorem gauss_moment_bound (k : ℕ) (beta : ℚ) (hbeta : 0 < beta) (u : ℝ) :
    |u| ^ k * Real.exp (-(beta : ℝ) * u^2) ≤ (gaussMoment k beta : ℝ) := by
  have sq := abs_pow_mul_exp_neg_sq_le k beta hbeta u
  have target := gaussMoment_sq_ge k beta hbeta
  have combined : (|u| ^ k * Real.exp (-(beta : ℝ) * u^2))^2 ≤
      ((gaussMoment k beta : ℝ))^2 := le_trans sq target
  exact (sq_le_sq₀ (by positivity) (by exact_mod_cast gaussMoment_nonneg k beta)).mp
    combined

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
