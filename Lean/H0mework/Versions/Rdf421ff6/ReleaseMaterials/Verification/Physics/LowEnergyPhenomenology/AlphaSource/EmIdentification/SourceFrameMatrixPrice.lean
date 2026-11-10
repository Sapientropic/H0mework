import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NativeActualLegPrice
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceFieldMatrixPriceOwn
open PreparationVacuumFullFieldRiesz ActualQuantitativePreparedFrameOwn
open GaussCoreHilbert
open scoped BigOperators InnerProductSpace
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

def matrixEnergy (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : ℝ :=
  ∑ i : FrameIndex F, ∑ j : FrameIndex F, ((entries i j).re ^ 2 + (entries i j).im ^ 2)

def matrixPrice (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : ℝ :=
  Real.sqrt (matrixEnergy F entries)

theorem matrixEnergy_norm_square (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) :
    matrixEnergy F entries = ∑ i, ∑ j, ‖entries i j‖ ^ 2 := by
  unfold matrixEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq (entries i j)

theorem matrixPrice_nonnegative (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) : 0 ≤ matrixPrice F entries := Real.sqrt_nonneg _

theorem original_frame_total_mass (F : GaussUnitaryHistory.Index) :
    (∑ i : FrameIndex F, ‖frameVector F i‖ ^ 2) = (Module.finrank ℂ (SourceSpan F) : ℝ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [frameVector]
  simp_rw [NativeHistoryGrade.norm_resolution]
  change (∑ j : BasisIndex F, ‖((sourceBasis F j : SourceSpan F) : H)‖ ^ 2) = _
  have unit (j : BasisIndex F) : ‖((sourceBasis F j : SourceSpan F) : H)‖ = 1 :=
    (sourceBasis F).norm_eq_one j
  simp only [unit, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, BasisIndex]

theorem original_frame_pair_mass (F : GaussUnitaryHistory.Index) (x y : H) :
    (∑ i : FrameIndex F, ∑ j : FrameIndex F,
      (‖inner ℂ (frameVector F i) x‖ * ‖inner ℂ (frameVector F j) y‖)^2) ≤ ‖x‖^2 * ‖y‖^2 := by
  have identity : (∑ i : FrameIndex F, ∑ j : FrameIndex F,
      (‖inner ℂ (frameVector F i) x‖ * ‖inner ℂ (frameVector F j) y‖)^2) =
      (∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖^2) *
        (∑ j : FrameIndex F, ‖inner ℂ (frameVector F j) y‖^2) := by
    simp only [mul_pow]
    conv_rhs => rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  rw [identity]
  exact mul_le_mul (frameMoment_mass F x) (frameMoment_mass F y)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

theorem scalar_matrix_pair_price {ι κ : Type*} [Fintype ι] [Fintype κ]
    (entries : ι → κ → ℂ) (left : ι → ℂ) (right : κ → ℂ) :
    ‖∑ i, ∑ j, star (left i) * entries i j * right j‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖entries i j‖ ^ 2) *
        Real.sqrt ((∑ i, ‖left i‖ ^ 2) * (∑ j, ‖right j‖ ^ 2)) := by
  have triangle : ‖∑ i, ∑ j, star (left i) * entries i j * right j‖ ≤
      ∑ i, ∑ j, ‖entries i j‖ * (‖left i‖ * ‖right j‖) := by
    calc
      _ ≤ ∑ i, ∑ j, ‖star (left i) * entries i j * right j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, norm_mul, norm_star]
        ring
  have cs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × κ))
    (fun ij => ‖entries ij.1 ij.2‖) (fun ij => ‖left ij.1‖ * ‖right ij.2‖)
  have flatten (g : ι × κ → ℝ) : (∑ ij : ι × κ, g ij) = ∑ i : ι, ∑ j : κ, g (i, j) :=
    Fintype.sum_prod_type g
  rw [flatten, flatten, flatten] at cs
  have factor : (∑ i, ∑ j, (‖left i‖ * ‖right j‖)^2) =
      (∑ i, ‖left i‖^2) * (∑ j, ‖right j‖^2) := by
    simp only [mul_pow]
    conv_rhs => rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  rw [factor] at cs
  exact triangle.trans cs

theorem original_frame_matrix_pair_price (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) (x y : H) :
    ‖inner ℂ x (finiteRiesz F entries y)‖ ≤ matrixPrice F entries * ‖x‖ * ‖y‖ := by
  rw [finiteRiesz_pair]
  have scalar := scalar_matrix_pair_price entries
    (fun i => inner ℂ (frameVector F i) x) (fun j => inner ℂ (frameVector F j) y)
  have mass : (∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖^2) *
      (∑ j : FrameIndex F, ‖inner ℂ (frameVector F j) y‖^2) ≤ ‖x‖^2 * ‖y‖^2 :=
    mul_le_mul (frameMoment_mass F x) (frameMoment_mass F y)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have root : Real.sqrt ((∑ i : FrameIndex F, ‖inner ℂ (frameVector F i) x‖^2) *
      (∑ j : FrameIndex F, ‖inner ℂ (frameVector F j) y‖^2)) ≤ ‖x‖ * ‖y‖ :=
    (Real.sqrt_le_sqrt mass).trans_eq
      (by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)])
  exact scalar.trans ((mul_le_mul_of_nonneg_left root (Real.sqrt_nonneg _)).trans_eq
    (by simp only [matrixPrice, matrixEnergy_norm_square, mul_assoc]))

theorem original_frame_matrix_operator_price (F : GaussUnitaryHistory.Index)
    (entries : FrameIndex F → FrameIndex F → ℂ) : ‖finiteRiesz F entries‖ ≤ matrixPrice F entries := by
  apply ContinuousLinearMap.opNorm_le_bound _ (matrixPrice_nonnegative F entries)
  intro y
  by_cases zero : ‖finiteRiesz F entries y‖ = 0
  · rw [zero]
    exact mul_nonneg (matrixPrice_nonnegative F entries) (norm_nonneg _)
  · have h := original_frame_matrix_pair_price F entries (finiteRiesz F entries y) y
    have self : ‖inner ℂ (finiteRiesz F entries y) (finiteRiesz F entries y)‖ =
        ‖finiteRiesz F entries y‖^2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [self] at h
    have positive : 0 < ‖finiteRiesz F entries y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    apply (mul_le_mul_iff_right₀ positive).mp
    calc
      ‖finiteRiesz F entries y‖ * ‖finiteRiesz F entries y‖ = ‖finiteRiesz F entries y‖^2 :=
        (pow_two _).symm
      _ ≤ matrixPrice F entries * ‖finiteRiesz F entries y‖ * ‖y‖ := h
      _ = (matrixPrice F entries * ‖y‖) * ‖finiteRiesz F entries y‖ := mul_right_comm _ _ _
      _ = ‖finiteRiesz F entries y‖ * (matrixPrice F entries * ‖y‖) := mul_comm _ _

end LowEnergy.ActualSourceFieldMatrixPriceOwn
