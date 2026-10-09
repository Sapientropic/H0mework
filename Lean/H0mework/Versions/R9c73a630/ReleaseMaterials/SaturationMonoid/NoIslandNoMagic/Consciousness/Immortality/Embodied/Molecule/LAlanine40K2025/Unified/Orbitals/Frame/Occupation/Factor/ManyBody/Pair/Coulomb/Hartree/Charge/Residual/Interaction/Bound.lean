import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceCoulomb
open scoped BigOperators
noncomputable section

def interactionWeight (B : Matrix Basis Basis ℝ) : ℝ :=
  ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
    |B i k * normalizedRepulsion j l i k|

def interactionWeightRight (A : Matrix Basis Basis ℝ) : ℝ :=
  ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
    |A j l * normalizedRepulsion j l i k|

theorem interactionWeight_nonneg (B : Matrix Basis Basis ℝ) :
    0 ≤ interactionWeight B := by
  unfold interactionWeight
  positivity

theorem interactionWeightRight_nonneg (A : Matrix Basis Basis ℝ) :
    0 ≤ interactionWeightRight A := by
  unfold interactionWeightRight
  positivity

private theorem abs_fourfold_sum (f : Basis → Basis → Basis → Basis → ℝ) :
    |∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis, f i k j l| ≤
      ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis, |f i k j l| := by
  calc
    _ ≤ ∑ i : Basis, |∑ k : Basis, ∑ j : Basis, ∑ l : Basis, f i k j l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Basis, ∑ k : Basis, |∑ j : Basis, ∑ l : Basis, f i k j l| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, |∑ l : Basis, f i k j l| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
        (fun k _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun k _ => Finset.sum_le_sum
        (fun j _ => Finset.abs_sum_le_sum_abs _ _)))

theorem four_center_abs_le (A B : Matrix Basis Basis ℝ) (ε : ℝ)
    (hA : ∀ j l, |A j l| ≤ ε) :
    |fourCenter A B| ≤ ε * interactionWeight B := by
  have each (i k j l : Basis) :
      |A j l * B i k * normalizedRepulsion j l i k| ≤
        ε * |B i k * normalizedRepulsion j l i k| := by
    rw [mul_assoc,abs_mul]
    exact mul_le_mul_of_nonneg_right (hA j l) (abs_nonneg _)
  calc
    |fourCenter A B| ≤
        ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
          |A j l * B i k * normalizedRepulsion j l i k| := by
      exact abs_fourfold_sum _
    _ ≤ ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
          ε * |B i k * normalizedRepulsion j l i k| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => each i k j l))))
    _ = ε * interactionWeight B := by
      simp only [interactionWeight,Finset.mul_sum]

theorem four_center_abs_le_right (A B : Matrix Basis Basis ℝ) (ε : ℝ)
    (hB : ∀ i k, |B i k| ≤ ε) :
    |fourCenter A B| ≤ ε * interactionWeightRight A := by
  have each (i k j l : Basis) :
      |A j l * B i k * normalizedRepulsion j l i k| ≤
        ε * |A j l * normalizedRepulsion j l i k| := by
    calc
      _ = |B i k * (A j l * normalizedRepulsion j l i k)| := by congr 1; ring
      _ = |B i k| * |A j l * normalizedRepulsion j l i k| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB i k) (abs_nonneg _)
  calc
    |fourCenter A B| ≤
        ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
          |A j l * B i k * normalizedRepulsion j l i k| := by
      exact abs_fourfold_sum _
    _ ≤ ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
          ε * |A j l * normalizedRepulsion j l i k| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => each i k j l))))
    _ = ε * interactionWeightRight A := by
      simp only [interactionWeightRight,Finset.mul_sum]

theorem hartree_residual_abs_le (ε : ℝ) (hδ : ∀ i k, |deltaMatrix i k| ≤ ε) :
    |d3HartreeEnergy - directEnergy.re| ≤
      (1 / 2 : ℝ) * ε *
        (interactionWeight d3Matrix + interactionWeightRight occupationMatrix) := by
  rw [d3_occupation_hartree_residual]
  have left := four_center_abs_le deltaMatrix d3Matrix ε hδ
  have right := four_center_abs_le_right occupationMatrix deltaMatrix ε hδ
  calc
    |(1 / 2 : ℝ) *
        (fourCenter deltaMatrix d3Matrix +
          fourCenter occupationMatrix deltaMatrix)| ≤
      (1 / 2 : ℝ) *
        (|fourCenter deltaMatrix d3Matrix| +
          |fourCenter occupationMatrix deltaMatrix|) := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ε *
        (interactionWeight d3Matrix + interactionWeightRight occupationMatrix) := by
      calc
        _ ≤ (1 / 2 : ℝ) *
            (ε * interactionWeight d3Matrix +
              ε * interactionWeightRight occupationMatrix) :=
          mul_le_mul_of_nonneg_left (add_le_add left right) (by norm_num)
        _ = _ := by ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
