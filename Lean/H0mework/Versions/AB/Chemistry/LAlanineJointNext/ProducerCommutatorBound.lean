import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerCommutatorExact

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem actual_commutator_entry (i j : Basis) :
    (Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian) i j =
      (commutatorNumerator i j : ℂ) / 1000000000000000000000000 := by
  change (∑ k : Basis, ((Source.hamiltonianNumerator i k : ℂ) / 1000000000000) *
      ((HeldForce.Source.gammaNumerator k j : ℂ) / 1000000000000)) -
    (∑ k : Basis, ((HeldForce.Source.gammaNumerator i k : ℂ) / 1000000000000) *
      ((Source.hamiltonianNumerator k j : ℂ) / 1000000000000)) = _
  simp only [commutatorNumerator, Int.cast_sum, Int.cast_sub, Int.cast_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem commutator_entry_norm_sum :
    (∑ i : Basis, ∑ j : Basis,
      ‖(Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian) i j‖) =
        (commutatorMagnitude : ℝ) / 10 ^ 24 := by
  simp only [commutatorMagnitude, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [actual_commutator_entry]
  norm_num [norm_div, Complex.norm_intCast, Nat.cast_natAbs]

theorem actual_commutator_bound :
    ‖Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian‖ <
      (862 : ℝ) / 10 ^ 9 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum
    (Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian)
  change ‖Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian‖ ≤ _ at bound
  rw [commutator_entry_norm_sum, commutatorMagnitude_exact] at bound
  exact bound.trans_lt (by norm_num)

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
