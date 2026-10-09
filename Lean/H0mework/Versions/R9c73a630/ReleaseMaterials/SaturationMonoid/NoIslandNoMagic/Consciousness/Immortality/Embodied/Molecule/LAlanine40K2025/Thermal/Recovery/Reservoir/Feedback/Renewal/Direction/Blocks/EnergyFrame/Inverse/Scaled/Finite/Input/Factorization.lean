import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Body
import H0mework.Chemistry.LAlanineThermalDynamics.PairFlowFactorization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def singleUnitary (H : SystemMatrix ι) (hermitian : H.IsHermitian) (time : ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨hamiltonianFlow H time,hamiltonianFlow_unitary H hermitian time⟩

theorem free_pair_tensor (H : SystemMatrix ι) (time : ℝ) :
    NormedSpace.exp ((-Complex.I*(time : ℂ)) • Thermal.Dynamics.freePairH H)=
      Matrix.kronecker (hamiltonianFlow H time) (hamiltonianFlow H time) := by
  have split : (-Complex.I*(time : ℂ)) • Thermal.Dynamics.freePairH H=
      Matrix.kronecker (time • (-Complex.I • H)) (1 : SystemMatrix ι)+
      Matrix.kronecker (1 : SystemMatrix ι) (time • (-Complex.I • H)) := by
    ext i j
    simp only [Thermal.Dynamics.freePairH,jointHamiltonian,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
    ring
  rw [split,Load.Recovery.Control.exp_tensor_sum]
  rfl

theorem pair_unitary_factors (H : SystemMatrix ι) (hermitian : H.IsHermitian) (g time : ℝ) :
    Thermal.Dynamics.pairUnitary H hermitian g time=
      Quantum.localUnitary (singleUnitary H hermitian time) (singleUnitary H hermitian time)*Exchange.exchangeUnitary (g*time) := by
  apply Subtype.ext
  change Thermal.Dynamics.pairPropagatorMatrix H g time=_
  rw [Thermal.Dynamics.pairPropagatorMatrix_factorization,free_pair_tensor]
  rfl

theorem partial_swap_product (a b c d : ℝ) :
    (partialSwap a b : JointMatrix ι)*partialSwap c d=partialSwap (a*c-b*d) (a*d+b*c) := by
  simp only [partialSwap,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,Matrix.one_mul,Matrix.mul_one,swap_squared]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  push_cast
  linear_combination (b*d : ℂ)*(1 : JointMatrix ι) i j*Complex.I_sq

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
