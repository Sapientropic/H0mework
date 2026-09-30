import H0mework.Chemistry.LAlanineThermalDynamics.PairHamiltonian
import Mathlib.Tactic.Module

/-! # One Hamiltonian generates all exchange-ladder directions -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Source

open Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def difference (H : SystemMatrix ι) : JointMatrix ι :=
  Matrix.kronecker H 1 - Matrix.kronecker 1 H

def raising (H : SystemMatrix ι) : JointMatrix ι :=
  (1 / 2 : ℂ) • (difference H + swapOperator * difference H)

def pairHamiltonian (H : SystemMatrix ι) : JointMatrix ι := pairH H 1

theorem tensor_sides_commute (H : SystemMatrix ι) :
    Commute (Matrix.kronecker H (1 : SystemMatrix ι)) (Matrix.kronecker (1 : SystemMatrix ι) H) := by
  show _ * _ = _ * _
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem free_commutes_difference (H : SystemMatrix ι) :
    Commute (freePairH H) (difference H) :=
  ((Commute.refl _).add_left (tensor_sides_commute H).symm).sub_right
    ((tensor_sides_commute H).add_left (Commute.refl _))

theorem swap_difference_swap (H : SystemMatrix ι) :
    (swapOperator : JointMatrix ι) * difference H * swapOperator = -difference H := by
  simp only [difference, mul_sub, sub_mul, swap_kronecker_swap]
  module

theorem difference_swap (H : SystemMatrix ι) :
    difference H * swapOperator = -(swapOperator * difference H) := by
  have equal := congrArg (fun A : JointMatrix ι => swapOperator * A) (swap_difference_swap H)
  simp only [← Matrix.mul_assoc, swap_squared, Matrix.one_mul, mul_neg] at equal
  exact equal

theorem swap_raising (H : SystemMatrix ι) : (swapOperator : JointMatrix ι) * raising H = raising H := by
  simp only [raising, mul_smul_comm, mul_add, ← Matrix.mul_assoc, swap_squared, Matrix.one_mul]
  module

theorem raising_swap (H : SystemMatrix ι) : raising H * (swapOperator : JointMatrix ι) = -raising H := by
  simp only [raising, smul_mul_assoc, add_mul, swap_difference_swap, difference_swap]
  module

theorem free_commutes_raising (H : SystemMatrix ι) :
    Commute (freePairH H) (raising H) :=
  ((free_commutes_difference H).add_right
    ((freePairH_commute_swap H).mul_right (free_commutes_difference H))).smul_right (1 / 2 : ℂ)

theorem raising_energy_gap (H : SystemMatrix ι) :
    pairHamiltonian H * raising H - raising H * pairHamiltonian H = (2 : ℂ) • raising H := by
  simp only [pairHamiltonian, pairH, Complex.ofReal_one, one_smul, add_mul, mul_add,
    swap_raising, raising_swap]
  rw [(free_commutes_raising H).eq]
  module

omit [Fintype ι] in
theorem difference_hermitian (H : SystemMatrix ι) (hH : H.IsHermitian) : (difference H).IsHermitian := by
  change (difference H)ᴴ = difference H
  simp only [difference, Matrix.conjTranspose_sub, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    hH.eq, Matrix.conjTranspose_one]

theorem raising_add_adjoint (H : SystemMatrix ι) (hH : H.IsHermitian) :
    raising H + (raising H)ᴴ = difference H := by
  simp only [raising, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    (difference_hermitian H hH).eq, swap_adjoint, difference_swap]
  norm_num
  module

theorem difference_zero_commutes [Nonempty ι] (H B : SystemMatrix ι) (zero : difference H = 0) :
    Commute H B := by
  have equal : Matrix.kronecker H (1 : SystemMatrix ι) = Matrix.kronecker (1 : SystemMatrix ι) H :=
    sub_eq_zero.mp zero
  have comm : Commute (Matrix.kronecker H (1 : SystemMatrix ι)) (Matrix.kronecker B (1 : SystemMatrix ι)) := by
    rw [equal]
    show _ * _ = _ * _
    simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have products := comm.eq
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at products
  obtain ⟨k⟩ := ‹Nonempty ι›
  show H * B = B * H
  ext i j
  have entry := congrArg (fun A : JointMatrix ι => A (i, k) (j, k)) products
  simpa only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one] using entry

theorem raising_zero_commutes [Nonempty ι] (H B : SystemMatrix ι) (hH : H.IsHermitian)
    (zero : raising H = 0) : Commute H B := by
  have diff := raising_add_adjoint H hH
  rw [zero, Matrix.conjTranspose_zero, add_zero] at diff
  exact difference_zero_commutes H B diff.symm

end

end LAlanine40K2025.Thermal.Powered.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
