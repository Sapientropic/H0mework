import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Scaled
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Polar
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsMatrixFrobeniusOperatorBound
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.HamiltonianBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable section

theorem matrix_norm_from_entries (M : Matrix Basis Basis ℂ) (error : ℝ) (nonnegative : 0 ≤ error)
    (entry : ∀ i j, ‖M i j‖ ≤ error) : ‖M‖ ≤ 98*error := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by positivity)
  calc
    _ ≤ ∑ _i : Basis, ∑ _j : Basis, error^2 := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (entry i j) 2))
    _ = _ := by norm_num [Fintype.card_fin]; ring

theorem actual_residual_norm : ‖A*Q-Q*E‖ ≤ (3/10^12 : ℝ) := by
  have entry (i j : Basis) : ‖(A*Q-Q*E) i j‖ ≤ (3/10^14 : ℝ) := by
    rw [residual_entry,norm_div,Complex.norm_intCast]
    have bound : (|Spectral.Rows.read (Spectral.Rows.rowAt residualColumns j) i| : ℝ) ≤ 3*10^16 := by
      exact_mod_cast residual_entry_bound i j
    norm_num
    linarith
  have bound := matrix_norm_from_entries _ (3/10^14) (by norm_num) entry
  exact bound.trans (by norm_num)

theorem actual_gram_norm : ‖star Q*Q-1‖ ≤ (3/10^13 : ℝ) := by
  have entry (i j : Basis) : ‖(star Q*Q-1) i j‖ ≤ (3/10^15 : ℝ) := by
    rw [Matrix.sub_apply,actual_Gram_scaled]
    have reading : ((1/10^30 : ℂ) • Cast.complexMatrix gram) i j-(1 : Matrix Basis Basis ℂ) i j =
        ((gram i j-(if j=i then (10^30 : Int) else 0) : Int) : ℂ)/10^30 := by
      simp only [Matrix.smul_apply,smul_eq_mul,Cast.complexMatrix,Matrix.one_apply]
      by_cases same : i=j
      · subst j; norm_num; ring
      · simp [same,Ne.symm same]; ring
    rw [reading,norm_div,Complex.norm_intCast]
    have bound : (|gram i j-(if j=i then (10^30 : Int) else 0)| : ℝ) ≤ 3*10^15 := by
      exact_mod_cast gram_entry_bound i j
    split_ifs at bound ⊢ <;> norm_num at bound ⊢ <;> linarith
  exact (matrix_norm_from_entries _ (3/10^15) (by norm_num) entry).trans (by norm_num)

theorem actual_gram_close : ‖star Q*Q-1‖ < 1 := actual_gram_norm.trans_lt (by norm_num)

def actualUnitary : Matrix.unitaryGroup Basis ℂ := sourcePolar Q actual_gram_close

theorem actual_unitary_error : ‖(actualUnitary : Matrix Basis Basis ℂ)-Q‖ ≤ (3/10^13 : ℝ) :=
  (source_polar_error Q actual_gram_close).trans actual_gram_norm

theorem diagonal_norm : ‖E‖ ≤ 19 := by
  rw [E,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have bound : (|energies[i.val]!| : ℝ) ≤ 19*10^15 := by exact_mod_cast energy_bound i
  simp only [norm_div,Complex.norm_intCast]
  norm_num at bound ⊢
  linarith

theorem actual_source_diagonal_error :
    ‖star (actualUnitary : Matrix Basis Basis ℂ)*A*(actualUnitary : Matrix Basis Basis ℂ)-E‖ ≤
      (21/10^12 : ℝ) := by
  have bound := diagonalized_source_error A Q E actual_gram_close
  have sourceBound : ‖A‖ ≤ 40 := Load.Producer.StrictThermal.sourceHamiltonian_norm_le_forty
  calc
    _ ≤ _ := bound
    _ ≤ 3/10^12+(40+19)*(3/10^13) := by gcongr; exact actual_residual_norm; exact diagonal_norm; exact actual_gram_norm
    _ ≤ _ := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
