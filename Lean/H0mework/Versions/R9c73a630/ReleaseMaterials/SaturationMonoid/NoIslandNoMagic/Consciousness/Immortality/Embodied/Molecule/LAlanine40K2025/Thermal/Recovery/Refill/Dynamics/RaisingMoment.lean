import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Source.PreparationEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.TransitionProbability

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Moment

open Collision Powered.Source Load.Producer.HeatProbability
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem energy_adjoint (A rho : Matrix ι ι ℂ) (hermitian : rho.IsHermitian) :
    energy Aᴴ rho = energy A rho := by
  have read := congrArg Complex.re (Matrix.trace_conjTranspose (A * rho))
  rw [Matrix.conjTranspose_mul, hermitian.eq, Matrix.trace_mul_comm] at read
  exact read.trans (by simp [energy])

omit [DecidableEq ι] in
theorem squared_energy_nonnegative (A rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    0 ≤ energy (Aᴴ * A) rho := by
  have bound := (Complex.nonneg_iff.mp (positive.mul_mul_conjTranspose_same A).trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at bound
  exact bound

theorem mean_square_le (A rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) : (energy A rho) ^ 2 ≤ energy (Aᴴ * A) rho := by
  let m := energy A rho
  have bound := squared_energy_nonnegative (A - (m : ℂ) • 1) rho positive
  have expansion : (A - (m : ℂ) • 1)ᴴ * (A - (m : ℂ) • 1) =
      Aᴴ * A - (m : ℂ) • Aᴴ - (m : ℂ) • A + (m * m : ℂ) • 1 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    norm_num
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [expansion] at bound
  simp only [energy, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Matrix.one_mul, normalized, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_one, mul_zero] at bound
  have adjoint := energy_adjoint A rho positive.isHermitian
  change (Aᴴ * rho).trace.re = (A * rho).trace.re at adjoint
  change 0 ≤ (Aᴴ * A * rho).trace.re - m * (Aᴴ * rho).trace.re -
    m * (A * rho).trace.re + m * m at bound
  rw [adjoint] at bound
  change 0 ≤ energy (Aᴴ * A) rho - m * m - m * m + m * m at bound
  dsimp [m] at bound
  nlinarith

def observable (H : SystemMatrix ι) : JointMatrix ι := (raising H)ᴴ * raising H

theorem product_difference (H rho tau : SystemMatrix ι)
    (rhoTrace : rho.trace = 1) (tauTrace : tau.trace = 1) :
    energy (difference H) (Matrix.kronecker rho tau) = energy H rho - energy H tau := by
  simp only [difference, energy, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    Matrix.kronecker, ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_kronecker,
    rhoTrace, tauTrace, mul_one, one_mul]

theorem product_raising_mean (H rho tau : SystemMatrix ι) (hH : H.IsHermitian)
    (hRho : rho.PosSemidef) (hTau : tau.PosSemidef)
    (rhoTrace : rho.trace = 1) (tauTrace : tau.trace = 1) :
    2 * energy (raising H) (Matrix.kronecker rho tau) = energy H rho - energy H tau := by
  have read := congrArg (fun O => energy O (Matrix.kronecker rho tau)) (raising_add_adjoint H hH)
  simp only [energy, Matrix.add_mul, Matrix.trace_add, Complex.add_re] at read
  change energy (raising H) (Matrix.kronecker rho tau) +
    energy (raising H)ᴴ (Matrix.kronecker rho tau) = energy (difference H) (Matrix.kronecker rho tau) at read
  rw [energy_adjoint (raising H) (Matrix.kronecker rho tau) (hRho.kronecker hTau).isHermitian,
    product_difference H rho tau rhoTrace tauTrace] at read
  linarith

theorem swap_commutes_observable (H : SystemMatrix ι) :
    Commute (swapOperator : JointMatrix ι) (observable H) := by
  have adjoint := congrArg Matrix.conjTranspose (raising_swap H)
  simp only [Matrix.conjTranspose_mul, swap_adjoint, Matrix.conjTranspose_neg] at adjoint
  show swapOperator * ((raising H)ᴴ * raising H) = (raising H)ᴴ * raising H * swapOperator
  rw [← mul_assoc, adjoint, mul_assoc, raising_swap]
  simp

theorem free_commutes_observable (H : SystemMatrix ι) (hH : H.IsHermitian) :
    Commute (Dynamics.freePairH H) (observable H) := by
  have adjoint := (free_commutes_raising H).star_star
  have freeStar : star (Dynamics.freePairH H) = Dynamics.freePairH H :=
    (Dynamics.freePairH_hermitian H hH).eq
  rw [freeStar] at adjoint
  exact adjoint.mul_right (free_commutes_raising H)

theorem pair_commutes_observable (H : SystemMatrix ι) (hH : H.IsHermitian) (g : ℝ) :
    Commute (observable H) (Dynamics.pairH H g) :=
  ((free_commutes_observable H hH).add_left
    ((swap_commutes_observable H).smul_left (g : ℂ))).symm

theorem jointNext_moment (H rho tau : SystemMatrix ι) (c s : ℝ) (circle : c ^ 2 + s ^ 2 = 1) :
    energy (observable H) (jointNext rho tau c s) =
      energy (observable H) (Matrix.kronecker rho tau) := by
  let U : Matrix.unitaryGroup (ι × ι) ℂ := ⟨partialSwap c s, partialSwap_unitary c s circle⟩
  exact PreparationEnergy.commuting_energy _ _ U
    (((Commute.one_right _).smul_right (c : ℂ)).sub_right
      ((swap_commutes_observable H).symm.smul_right (Complex.I * (s : ℂ))))

theorem pairAdvance_moment (H : SystemMatrix ι) (hH : H.IsHermitian) (g t : ℝ)
    (rho : JointMatrix ι) :
    energy (observable H) (Dynamics.pairAdvance H g t rho) = energy (observable H) rho :=
  congrArg Complex.re (Dynamics.pairAdvance_conserved_of_commute H hH g t _ rho
    (pair_commutes_observable H hH g))

theorem source_before_field_moment_gt : (25 / 4 : ℝ) <
    energy (observable Thermal.Source.energyHamiltonian) Work.Drive.sourceFieldCycleCurrent := by
  rw [Work.Drive.sourceFieldCycleCurrent, Thermal.Producer.rememberedJoint]
  change (25 / 4 : ℝ) < energy (observable Thermal.Source.energyHamiltonian)
    (Dynamics.pairAdvance _ _ _ Thermal.Producer.generatedJoint)
  rw [pairAdvance_moment _ Thermal.Source.energyHamiltonian_hermitian]
  rw [Thermal.Producer.generatedJoint, jointNext_moment _ _ _ _ _ Thermal.Source.exchange_normalized]
  have mean := product_raising_mean Thermal.Source.energyHamiltonian _ _
    Thermal.Source.energyHamiltonian_hermitian Thermal.Source.systemCurrent_posSemidef
    Thermal.Source.bathCurrent_posSemidef Thermal.Source.systemCurrent_trace Thermal.Source.bathCurrent_trace
  have bound := mean_square_le (raising Thermal.Source.energyHamiltonian)
    (Matrix.kronecker Thermal.Source.systemCurrent Thermal.Source.bathCurrent)
    (Thermal.Source.systemCurrent_posSemidef.kronecker Thermal.Source.bathCurrent_posSemidef)
    (by rw [Matrix.kronecker, Matrix.trace_kronecker, Thermal.Source.systemCurrent_trace,
      Thermal.Source.bathCurrent_trace, mul_one])
  change _ ≤ energy (observable _) _ at bound
  nlinarith [PreparationEnergy.source_mean_gap_gt_five]

end
end LAlanine40K2025.Thermal.Recovery.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
