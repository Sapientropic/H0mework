import H0mework.Chemistry.LAlanineRefinementDensity.DensityModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

open Finset
open scoped BigOperators

variable {Basis : Type*} [Fintype Basis]

def jetOrder (d : MultiIndex) : Nat := d 0 + d 1 + d 2

theorem jetOrder_raise (d : MultiIndex) (axis : Fin 3) : jetOrder (raise d axis) = jetOrder d + 1 := by
  fin_cases axis <;> simp [jetOrder, raise, Function.update] <;> omega

noncomputable section

def bilinearEnvelope (matrixBound : Basis → Basis → ℚ) (bounds : MultiIndex → Basis → ℚ)
    (left right : MultiIndex) : ℚ := ∑ i, ∑ j, matrixBound i j * bounds left i * bounds right j

def secondEnvelope (matrixBound : Basis → Basis → ℚ) (bounds : MultiIndex → Basis → ℚ)
    (left right : MultiIndex) (axis : Fin 3) : ℚ :=
  bilinearEnvelope matrixBound bounds (raise (raise left axis) axis) right +
    2 * bilinearEnvelope matrixBound bounds (raise left axis) (raise right axis) +
      bilinearEnvelope matrixBound bounds left (raise (raise right axis) axis)

def fourthEnvelope (matrixBound : Basis → Basis → ℚ) (bounds : MultiIndex → Basis → ℚ)
    (left right : MultiIndex) (firstAxis secondAxis : Fin 3) : ℚ :=
  secondEnvelope matrixBound bounds (raise (raise left firstAxis) firstAxis) right secondAxis +
    2 * secondEnvelope matrixBound bounds (raise left firstAxis) (raise right firstAxis) secondAxis +
      secondEnvelope matrixBound bounds left (raise (raise right firstAxis) firstAxis) secondAxis

def laplacianSecondEnvelope (matrixBound : Basis → Basis → ℚ) (bounds : MultiIndex → Basis → ℚ)
    (axis : Fin 3) : ℚ :=
  ∑ innerAxis : Fin 3, fourthEnvelope matrixBound bounds (fun _ => 0) (fun _ => 0) innerAxis axis

theorem bilinear_abs_bound (orbitals : Basis → List Term) (matrix matrixBound : Basis → Basis → ℚ)
    (bounds : MultiIndex → Basis → ℚ) (left right : MultiIndex) (x : Point)
    (matrixBounded : ∀ i j, |matrix i j| ≤ matrixBound i j)
    (leftBounded : ∀ i, |orbital (orbitals i) left x| ≤ (bounds left i : ℝ))
    (rightBounded : ∀ i, |orbital (orbitals i) right x| ≤ (bounds right i : ℝ)) :
    |bilinear orbitals matrix left right x| ≤ (bilinearEnvelope matrixBound bounds left right : ℝ) := by
  unfold bilinear bilinearEnvelope
  simp only [Rat.cast_sum, Rat.cast_mul]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [abs_mul, abs_mul]
  have hm : |(matrix i j : ℝ)| ≤ (matrixBound i j : ℝ) := by exact_mod_cast matrixBounded i j
  have mn := (abs_nonneg _).trans hm
  have ln := (abs_nonneg _).trans (leftBounded i)
  exact mul_le_mul (mul_le_mul hm (leftBounded i) (abs_nonneg _) mn)
    (rightBounded j) (abs_nonneg _) (mul_nonneg mn ln)

private theorem abs_three (a b c A B C : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + 2 * b + c| ≤ A + 2 * B + C := by
  have middle : |2 * b| = 2 * |b| := by norm_num [abs_mul]
  have pair := abs_add_le a (2 * b)
  have total := abs_add_le (a + 2 * b) c
  rw [middle] at pair
  linarith

theorem secondBilinear_abs_bound (orbitals : Basis → List Term) (matrix matrixBound : Basis → Basis → ℚ)
    (bounds : MultiIndex → Basis → ℚ) (left right : MultiIndex) (x : Point) (axis : Fin 3)
    (order : jetOrder left + jetOrder right + 2 ≤ 4)
    (matrixBounded : ∀ i j, |matrix i j| ≤ matrixBound i j)
    (jetsBounded : ∀ d, jetOrder d ≤ 4 → ∀ i, |orbital (orbitals i) d x| ≤ (bounds d i : ℝ)) :
    |secondBilinear orbitals matrix left right axis x| ≤ (secondEnvelope matrixBound bounds left right axis : ℝ) := by
  have pair (l r : MultiIndex) (sumOrder : jetOrder l + jetOrder r ≤ 4) :=
    bilinear_abs_bound orbitals matrix matrixBound bounds l r x matrixBounded
      (jetsBounded l (by omega)) (jetsBounded r (by omega))
  simp only [secondBilinear, secondEnvelope, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  apply abs_three
  · exact pair _ _ (by simp only [jetOrder_raise]; omega)
  · exact pair _ _ (by simp only [jetOrder_raise]; omega)
  · exact pair _ _ (by simp only [jetOrder_raise]; omega)

theorem fourthBilinear_abs_bound (orbitals : Basis → List Term) (matrix matrixBound : Basis → Basis → ℚ)
    (bounds : MultiIndex → Basis → ℚ) (left right : MultiIndex) (x : Point) (firstAxis secondAxis : Fin 3)
    (order : jetOrder left + jetOrder right + 4 ≤ 4)
    (matrixBounded : ∀ i j, |matrix i j| ≤ matrixBound i j)
    (jetsBounded : ∀ d, jetOrder d ≤ 4 → ∀ i, |orbital (orbitals i) d x| ≤ (bounds d i : ℝ)) :
    |fourthBilinear orbitals matrix left right firstAxis secondAxis x| ≤
      (fourthEnvelope matrixBound bounds left right firstAxis secondAxis : ℝ) := by
  simp only [fourthBilinear, fourthEnvelope, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  apply abs_three
  · exact secondBilinear_abs_bound orbitals matrix matrixBound bounds _ _ x secondAxis
      (by simp only [jetOrder_raise]; omega) matrixBounded jetsBounded
  · exact secondBilinear_abs_bound orbitals matrix matrixBound bounds _ _ x secondAxis
      (by simp only [jetOrder_raise]; omega) matrixBounded jetsBounded
  · exact secondBilinear_abs_bound orbitals matrix matrixBound bounds _ _ x secondAxis
      (by simp only [jetOrder_raise]; omega) matrixBounded jetsBounded

theorem laplacianSecond_abs_bound (orbitals : Basis → List Term) (matrix matrixBound : Basis → Basis → ℚ)
    (bounds : MultiIndex → Basis → ℚ) (x : Point) (axis : Fin 3)
    (matrixBounded : ∀ i j, |matrix i j| ≤ matrixBound i j)
    (jetsBounded : ∀ d, jetOrder d ≤ 4 → ∀ i, |orbital (orbitals i) d x| ≤ (bounds d i : ℝ)) :
    |laplacianSecond orbitals matrix axis x| ≤ (laplacianSecondEnvelope matrixBound bounds axis : ℝ) := by
  unfold laplacianSecond laplacianSecondEnvelope
  rw [Rat.cast_sum]
  exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun innerAxis _ =>
    fourthBilinear_abs_bound orbitals matrix matrixBound bounds _ _ x innerAxis axis
      (by decide) matrixBounded jetsBounded))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
