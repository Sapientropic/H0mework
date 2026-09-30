import H0mework.Chemistry.LAlanineJointNext.ProducerElectronic
import H0mework.Chemistry.LAlanineJointNext.ProducerNormBounds
import H0mework.Chemistry.LAlanineJointNext.ProducerRealizationNorm

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def phaseTarget : Matrix Basis Basis ℂ :=
  Unitary.conjStarAlgAut ℂ _ (Math.frozenUnitary Source.hamiltonian sourceHamiltonian_hermitian (Interface.duration : ℝ))
    HeldForce.Source.realizedHeld

theorem actual_duration_bound : |(Interface.duration : ℝ)| < (432 : ℝ) / 10 ^ 6 := by
  have positive : (0 : ℝ) < (Interface.duration : ℝ) := by exact_mod_cast Interface.one_elapsed_clock.2
  rw [abs_of_pos positive]
  change (Propagation.Producer.nativeClockStep : ℝ) < _
  rw [Propagation.Producer.nativeClockStep_exact]
  norm_num

theorem source_geometric_displacement : ‖realizedInputTarget - phaseTarget‖ < (990 : ℝ) / 10 ^ 12 := by
  have bound := HeldForce.Producer.conjugation_displacement
    (ElectronicFrame.Polar.matrix Source.crossMatrix) phaseTarget
    (ElectronicFrame.Polar.matrix_mem_unitary _ sourceCross_close)
  change ‖realizedInputTarget - phaseTarget‖ ≤ _ at bound
  have phaseNorm : ‖phaseTarget‖ = ‖HeldForce.Source.realizedHeld‖ := StarAlgEquiv.norm_map _ _
  rw [phaseNorm] at bound
  have close := geometric_unitary_close
  have input := realized_input_norm
  have product : 2 * ‖ElectronicFrame.Polar.matrix Source.crossMatrix - 1‖ * ‖HeldForce.Source.realizedHeld‖ <
      2 * ((45 : ℝ) / 10 ^ 12) * 11 := by
    gcongr
  exact bound.trans_lt (by norm_num at product ⊢; exact product)


end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
