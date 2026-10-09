import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Corners
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Environment

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision Load.Source Powered.Dynamics
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def preparationIndex (e : Fin 2) (i : ι) : (ι × Fin 2) × Fin 2 := ((i,1),e)

def preparationObservable (O : Matrix ((ι × Fin 2) × Fin 2) ((ι × Fin 2) × Fin 2) ℂ) : Matrix ι ι ℂ :=
  ∑ e : Fin 2,(environmentPMF e).toReal • O.submatrix (preparationIndex e) (preparationIndex e)

omit [Fintype ι] [DecidableEq ι] in
theorem preparation_index_injective (e : Fin 2) : Function.Injective (preparationIndex (ι := ι) e) :=
  fun _ _ same => congrArg (fun p => p.1.1) same

theorem preparation_observable_norm (O : Matrix ((ι × Fin 2) × Fin 2) ((ι × Fin 2) × Fin 2) ℂ)
    (hermitian : O.IsHermitian) : ‖preparationObservable O‖ ≤ ‖O‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ e : Fin 2,(environmentPMF e).toReal*‖O.submatrix (preparationIndex e) (preparationIndex e)‖ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [norm_smul,Real.norm_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ e : Fin 2,(environmentPMF e).toReal*‖O‖ := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (principal_norm (preparationIndex e) (preparation_index_injective e) O hermitian) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul,Population.pmf_sum_toReal,one_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem preparation_observable_hermitian (O : Matrix ((ι × Fin 2) × Fin 2) ((ι × Fin 2) × Fin 2) ℂ)
    (hermitian : O.IsHermitian) : (preparationObservable O).IsHermitian := by
  rw [preparationObservable,Fin.sum_univ_two]
  exact ((hermitian.submatrix (preparationIndex 0)).smul (k := (environmentPMF 0).toReal) (by rfl)).add
    ((hermitian.submatrix (preparationIndex 1)).smul (k := (environmentPMF 1).toReal) (by rfl))

omit [DecidableEq ι] in
theorem preparation_energy (O : Matrix ((ι × Fin 2) × Fin 2) ((ι × Fin 2) × Fin 2) ℂ) (rho : Matrix ι ι ℂ) :
    energy O (Matrix.kronecker (chargedInput rho) environmentState)=energy (preparationObservable O) rho := by
  unfold energy
  congr 1
  simp only [preparationObservable,Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,Matrix.trace_smul]
  simp only [chargedInput,environmentState,excitedController,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.diagonal_apply,
    Matrix.submatrix_apply,preparationIndex]
  simp
  simp_rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
