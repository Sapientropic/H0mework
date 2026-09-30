import H0mework.Chemistry.LAlanineReentry.ProducerCalculationComplexCommutatorBound

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.PhaseConsumer

open Propagation.Interface JointNext.RealRestriction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

/-- The population-coordinate readout of the source Hamiltonian's Liouville right-hand side. -/
def signal (D : Matrix Basis Basis ℂ) : ℝ :=
  (-Complex.I * (Source.hamiltonian * D - D * Source.hamiltonian) 0 0).re

theorem actual_phase_derivative :
    HasDerivAt (fun time => Unitary.conjStarAlgAut ℂ _
      (JointNext.Math.frozenUnitary Source.hamiltonian Producer.sourceHamiltonian_hermitian time)
        Source.currentRealized)
      (-Complex.I • (Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian)) 0 := by
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, JointNext.Math.frozenUnitary_eq_exp,
    zero_smul, NormedSpace.exp_zero, one_mul, star_one, mul_one] using
    JointNext.EvolutionBound.conjugated_hasDerivAt Source.hamiltonian Producer.sourceHamiltonian_hermitian
      Source.currentRealized 0

private theorem scaled_signal (real imaginary : Int) :
    (-Complex.I * (((real : ℂ) + Complex.I * (imaginary : ℂ)) / 10 ^ 27)).re =
      (imaginary : ℝ) / 10 ^ 27 := by
  norm_num [Complex.mul_re, Complex.div_im]

theorem source_imaginary_contraction : Producer.commutatorImagNumerator 0 0 = 932113280398422 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem actual_signal : signal Source.currentRealized = (932113280398422 : ℝ) / 10 ^ 27 := by
  rw [signal, Producer.actual_commutator_entry, scaled_signal]
  exact congrArg (fun n : Int => (n : ℝ) / 10 ^ 27) source_imaginary_contraction

theorem hamiltonian_imaginary_zero (i j : Basis) : (Source.hamiltonian i j).im = 0 := by
  change ((Source.hamiltonianNumerator i j : ℂ) / 1000000000000).im = 0
  simp

theorem complexified_signal_zero (A : Matrix Basis Basis ℝ) : signal (complexify A) = 0 := by
  simp only [signal, Complex.neg_re, Complex.I_re, Complex.I_im,
    Complex.mul_re, zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
  simp only [Matrix.sub_apply, Complex.sub_im, Matrix.mul_apply, Complex.im_sum, Complex.mul_im,
    complexify, Matrix.map_apply, Complex.ofReal_im, hamiltonian_imaginary_zero,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero, sub_self]

theorem same_real_input :
    JointNext.RealRestriction.realPart (complexify (JointNext.RealRestriction.realPart Source.currentRealized)) =
      JointNext.RealRestriction.realPart Source.currentRealized := by
  ext i j
  rfl

theorem actual_signal_not_zero : signal Source.currentRealized ≠ 0 := by
  rw [actual_signal]
  norm_num

/-- Real-only ingress loses a registered response of this actual current, not just a synthetic fixture. -/
theorem actual_phaseSignal_not_factor_through_realPart :
    ¬∃ readSignal : Matrix Basis Basis ℝ → ℝ, ∀ D, signal D = readSignal (JointNext.RealRestriction.realPart D) := by
  rintro ⟨readSignal, reads⟩
  have actual := reads Source.currentRealized
  have erased := reads (complexify (JointNext.RealRestriction.realPart Source.currentRealized))
  rw [complexified_signal_zero, same_real_input] at erased
  exact actual_signal_not_zero (actual.trans erased.symm)

end
end LAlanine40K2025.Reentry.PhaseConsumer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
