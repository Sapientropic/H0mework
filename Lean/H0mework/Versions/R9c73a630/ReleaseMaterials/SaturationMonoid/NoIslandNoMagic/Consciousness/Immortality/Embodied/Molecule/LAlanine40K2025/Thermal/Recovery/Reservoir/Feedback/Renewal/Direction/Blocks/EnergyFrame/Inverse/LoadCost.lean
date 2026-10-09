import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.PCNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.NetResponse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Load.Source Powered.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem pair_exchange_commute (H : Matrix Pair Pair ℂ) :
    Commute (Matrix.kronecker (Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)) (1 : Matrix (Fin 2) (Fin 2) ℂ)) loadInteraction := by
  let e := Equiv.prodAssoc Pair (Fin 2) (Fin 2)
  have read : Matrix.kronecker (Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ)) (1 : Matrix (Fin 2) (Fin 2) ℂ)=
      (Matrix.kronecker H (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).submatrix e e := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.submatrix_apply,e,Equiv.prodAssoc_apply]
    rw [show (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (i.1.2,i.2) (j.1.2,j.2)=
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i.1.2 j.1.2*(1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j.2 by
        simp only [Matrix.one_apply]; split_ifs <;> simp_all]
    ring
  rw [read]
  change (Matrix.kronecker H 1).submatrix e e*(Matrix.kronecker 1 controllerEnvironmentExchange).submatrix e e=
    (Matrix.kronecker 1 controllerEnvironmentExchange).submatrix e e*(Matrix.kronecker H 1).submatrix e e
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,(one_tensor_commutes H controllerEnvironmentExchange).eq]

def numericActivePC : Matrix PairController PairController ℂ :=
  Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Powered.Dynamics.controllerHamiltonian 2)+interaction E

theorem numeric_active_PC_norm : ‖numericActivePC‖ ≤ 50 := by
  have controller := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := Pair) (κ := Fin 2)) (Powered.Dynamics.controllerHamiltonian 2)
  change ‖Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Powered.Dynamics.controllerHamiltonian 2)‖ ≤ _ at controller
  have bound := norm_add_le (Matrix.kronecker (1 : Matrix Pair Pair ℂ) (Powered.Dynamics.controllerHamiltonian 2)) (interaction E)
  exact bound.trans (by linarith [controllerHamiltonian_norm_le,numeric_interaction_norm])

theorem numeric_load_commutator_bound : ‖loadInteraction*numericLoadPC-numericLoadPC*loadInteraction‖ ≤ 100 := by
  let active : LoadedJoint := Matrix.kronecker numericActivePC (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let bare : LoadedJoint := Matrix.kronecker (Matrix.kronecker (pairHamiltonian E) (1 : Matrix (Fin 2) (Fin 2) ℂ)) (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have split : numericLoadPC=bare+active := by
    ext i j
    simp only [numericLoadPC,sourcePCH,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
      numericActivePC,bare,active,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply]
    ring
  have commute : bare*loadInteraction=loadInteraction*bare := (pair_exchange_commute (pairHamiltonian E)).eq
  have delta : loadInteraction*numericLoadPC-numericLoadPC*loadInteraction=loadInteraction*active-active*loadInteraction := by
    rw [split,mul_add,add_mul,commute]
    abel
  have norm : ‖active‖ ≤ 50 := (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) _).trans numeric_active_PC_norm
  rw [delta]
  have left := norm_mul_le loadInteraction active
  have right := norm_mul_le active loadInteraction
  apply (norm_sub_le _ _).trans
  nlinarith [actual_load_interaction_norm,norm_nonneg loadInteraction,norm_nonneg active]

theorem original_load_cost : loadResponseCost ≤ 101 := by
  unfold loadResponseCost
  linarith [numeric_load_commutator_bound]

theorem original_exchange_cost : exchangeResponseCost ≤ 180 := by
  unfold exchangeResponseCost
  linarith [original_PC_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
