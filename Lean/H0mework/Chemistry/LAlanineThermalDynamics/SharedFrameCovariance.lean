import H0mework.Chemistry.LAlanineThermalDynamics.ExchangeLadder
import H0mework.Chemistry.LAlanineEntropy.PartialTraceCovariance

/-! # The source raising operator is natural under every shared frame, not a chosen mode number -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Source

open Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

theorem shared_conjugation_difference (U : Matrix.unitaryGroup ι ℂ) (H : SystemMatrix ι) :
    Quantum.localConjugation U U (difference H) = difference (Quantum.conjugation U H) := by
  have one : Quantum.conjugation U (1 : SystemMatrix ι) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ _ U)
  simp only [difference, map_sub, Quantum.localConjugation_tensor, one]

theorem swap_commutes_shared (U : Matrix.unitaryGroup ι ℂ) :
    Commute (swapOperator : JointMatrix ι) (Quantum.localUnitary U U : JointMatrix ι) := by
  show _ * _ = _ * _
  have equal := congrArg (fun A : JointMatrix ι => A * swapOperator)
    (swap_kronecker_swap (U : SystemMatrix ι) (U : SystemMatrix ι))
  simp only [Matrix.mul_assoc, swap_squared, Matrix.mul_one] at equal
  exact equal

theorem shared_conjugation_swap (U : Matrix.unitaryGroup ι ℂ) :
    Quantum.localConjugation U U (swapOperator : JointMatrix ι) = swapOperator := by
  change (Quantum.localUnitary U U : JointMatrix ι) * swapOperator *
    star (Quantum.localUnitary U U : JointMatrix ι) = _
  rw [← (swap_commutes_shared U).eq, Matrix.mul_assoc,
    Unitary.mul_star_self_of_mem (Quantum.localUnitary U U).property, Matrix.mul_one]

theorem shared_conjugation_raising (U : Matrix.unitaryGroup ι ℂ) (H : SystemMatrix ι) :
    Quantum.localConjugation U U (raising H) = raising (Quantum.conjugation U H) := by
  let phi := Unitary.conjStarAlgAut ℂ _ (Quantum.localUnitary U U)
  have swap : phi (swapOperator : JointMatrix ι) = swapOperator := shared_conjugation_swap U
  have diff : phi (difference H) = difference (Quantum.conjugation U H) :=
    shared_conjugation_difference U H
  change phi (raising H) = _
  simp only [raising, map_smul, map_add, map_mul, swap, diff]

omit [Fintype ι] in
theorem diagonal_difference (energies : ι → ℝ) :
    difference (Matrix.diagonal (fun i => (energies i : ℂ))) =
      Matrix.diagonal (fun ia : ι × ι => ((energies ia.1 - energies ia.2 : ℝ) : ℂ)) := by
  unfold difference
  simp only [Matrix.kronecker]
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_sub]
  congr 1
  ext ia
  simp

theorem diagonal_raising_apply (energies : ι → ℝ) (i a j b : ι) :
    raising (Matrix.diagonal (fun k => (energies k : ℂ))) (i, a) (j, b) =
      (1 / 2 : ℂ) *
        ((if i = j ∧ a = b then ((energies i - energies a : ℝ) : ℂ) else 0) -
          (if a = j ∧ i = b then ((energies i - energies a : ℝ) : ℂ) else 0)) := by
  simp only [raising, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, diagonal_difference,
    swap_mul_apply, Matrix.diagonal_apply, Prod.mk.injEq, Complex.ofReal_sub]
  split_ifs <;> ring


end

end LAlanine40K2025.Thermal.Powered.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
