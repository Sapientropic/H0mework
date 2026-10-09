import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Channels
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
open Powered.Dynamics
open scoped BigOperators
variable {α : Type*} [Fintype α]

def chargedInjection (i : α × Fin 2) : (α × Fin 2) × Fin 2 := ((i.1,1),i.2)

theorem charged_environment_energy (O : Matrix ((α × Fin 2) × Fin 2) ((α × Fin 2) × Fin 2) ℂ)
    (ρ : Matrix α α ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    Collision.energy O (Matrix.kronecker (chargedInput ρ) σ)=
      Collision.energy (O.submatrix chargedInjection chargedInjection) (Matrix.kronecker ρ σ) := by
  norm_num [Collision.energy,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,
    chargedInput,excitedController,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.submatrix_apply,
    chargedInjection,Fin.sum_univ_two,Matrix.diagonal_apply]

theorem diagonal_charged_energy (O : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (z : ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    Collision.energy O (Matrix.kronecker (z • excitedController) σ)=
      Collision.energy (O.submatrix (fun e => (1,e)) (fun e => (1,e))) (z • σ) := by
  norm_num [Collision.energy,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,
    excitedController,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.submatrix_apply,
    Fin.sum_univ_two,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
