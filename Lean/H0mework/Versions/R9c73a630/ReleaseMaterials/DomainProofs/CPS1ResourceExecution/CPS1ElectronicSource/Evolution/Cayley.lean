import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution
noncomputable section
open scoped Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

def generator (H : Matrix n n ℂ) (time : ℝ) : Matrix n n ℂ :=
  (Complex.I * (time : ℂ)) • H

def denominator (H : Matrix n n ℂ) (time : ℝ) : Matrix n n ℂ :=
  1 + generator H time

def step (H : Matrix n n ℂ) (time : ℝ) : Matrix n n ℂ :=
  (denominator H time)⁻¹ * (denominator H time).conjTranspose

omit [Fintype n] [DecidableEq n] in
theorem generator_skew (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    (generator H time).conjTranspose = -(generator H time) := by
  simp only [generator,Matrix.conjTranspose_smul,hermitian.eq,star_mul,
    Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  rw [mul_neg,mul_comm (time : ℂ),neg_smul]

theorem denominator_normal (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    (denominator H time).conjTranspose * denominator H time =
      denominator H time * (denominator H time).conjTranspose := by
  simp only [denominator,Matrix.conjTranspose_add,Matrix.conjTranspose_one,
    generator_skew H hermitian time]
  noncomm_ring

theorem denominator_positive (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    ((denominator H time).conjTranspose * denominator H time).PosDef := by
  have identity : (denominator H time).conjTranspose * denominator H time =
      1 + (generator H time).conjTranspose * generator H time := by
    simp only [denominator,Matrix.conjTranspose_add,Matrix.conjTranspose_one,
      generator_skew H hermitian time]
    noncomm_ring
  rw [identity]
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

theorem denominator_unit (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    IsUnit (denominator H time) := by
  have product := (denominator_positive H hermitian time).isUnit
  have determinant := (Matrix.isUnit_iff_isUnit_det _).mp product
  rw [Matrix.det_mul] at determinant
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right determinant)

theorem step_unitary (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    step H time ∈ unitary (Matrix n n ℂ) := by
  have sourceUnit := denominator_unit H hermitian time
  have inverseUnit : IsUnit (denominator H time)⁻¹ :=
    Matrix.isUnit_nonsing_inv_iff.mpr sourceUnit
  have adjointUnit : IsUnit (denominator H time).conjTranspose :=
    sourceUnit.star
  have actualUnit : IsUnit (step H time) := inverseUnit.mul adjointUnit
  apply actualUnit.mem_unitary_of_mul_star_self
  change step H time * (step H time).conjTranspose = 1
  simp only [step,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_nonsing_inv]
  have determinant := (Matrix.isUnit_iff_isUnit_det _).mp sourceUnit
  have adjointDet := (Matrix.isUnit_iff_isUnit_det _).mp adjointUnit
  calc
    _ = (denominator H time)⁻¹ *
        ((denominator H time).conjTranspose * denominator H time) *
        ((denominator H time).conjTranspose)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (denominator H time)⁻¹ *
        (denominator H time * (denominator H time).conjTranspose) *
        ((denominator H time).conjTranspose)⁻¹ := by rw [denominator_normal H hermitian time]
    _ = 1 := by
      rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ determinant,Matrix.one_mul,
        Matrix.mul_nonsing_inv _ adjointDet]

theorem actual_equation (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    denominator H time * step H time = 1-generator H time := by
  have determinant := (Matrix.isUnit_iff_isUnit_det _).mp (denominator_unit H hermitian time)
  rw [step,← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ determinant,Matrix.one_mul]
  simp only [denominator,Matrix.conjTranspose_add,Matrix.conjTranspose_one,
    generator_skew H hermitian time,sub_eq_add_neg]

theorem zero_time (H : Matrix n n ℂ) : step H 0 = 1 := by
  simp [step,denominator,generator]

variable {m : Type*}
def occupiedUpdate (H : Matrix n n ℂ) (time : ℝ) (occupied : Matrix n m ℂ) : Matrix n m ℂ :=
  step H time * occupied

theorem occupied_gram (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (occupied : Matrix n m ℂ) :
    (occupiedUpdate H time occupied).conjTranspose * occupiedUpdate H time occupied =
      occupied.conjTranspose * occupied := by
  have unitary := (step_unitary H hermitian time).1
  change (step H time).conjTranspose * step H time = 1 at unitary
  simp only [occupiedUpdate,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (step H time).conjTranspose,unitary,Matrix.one_mul]

def densityUpdate (H : Matrix n n ℂ) (time : ℝ) (density : Matrix n n ℂ) : Matrix n n ℂ :=
  step H time * density * (step H time).conjTranspose

theorem density_hermitian (H : Matrix n n ℂ) (time : ℝ)
    (density : Matrix n n ℂ) (source : density.IsHermitian) :
    (densityUpdate H time density).IsHermitian := by
  unfold densityUpdate
  exact Matrix.isHermitian_mul_mul_conjTranspose _ source

theorem density_idempotent (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (density : Matrix n n ℂ) (source : density * density = density) :
    densityUpdate H time density * densityUpdate H time density = densityUpdate H time density := by
  have unitary := (step_unitary H hermitian time).1
  change (step H time).conjTranspose * step H time = 1 at unitary
  simp only [densityUpdate,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (step H time).conjTranspose,unitary,Matrix.one_mul,
    ← Matrix.mul_assoc density,source]

theorem electron_number (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (density : Matrix n n ℂ) :
    Matrix.trace (densityUpdate H time density) = Matrix.trace density := by
  have unitary := (step_unitary H hermitian time).1
  change (step H time).conjTranspose * step H time = 1 at unitary
  rw [densityUpdate,Matrix.trace_mul_cycle,unitary,Matrix.one_mul]

theorem inverse_commutes (A B : Matrix n n ℂ) (unit : IsUnit A) (commutes : A * B = B * A) :
    A⁻¹ * B = B * A⁻¹ := by
  have determinant := (Matrix.isUnit_iff_isUnit_det _).mp unit
  calc
    _ = A⁻¹ * B * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ determinant,Matrix.mul_one]
    _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * (A * B) * A⁻¹ := by rw [commutes]
    _ = B * A⁻¹ := by
      rw [← Matrix.mul_assoc A⁻¹,Matrix.nonsing_inv_mul _ determinant,Matrix.one_mul]

theorem step_hamiltonian (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ) :
    step H time * H = H * step H time := by
  have generatorComm : generator H time * H = H * generator H time := by
    simp only [generator,Matrix.smul_mul,Matrix.mul_smul]
  have denominatorComm : denominator H time * H = H * denominator H time := by
    simp only [denominator,Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,generatorComm]
  have inverseComm := inverse_commutes (denominator H time) H
    (denominator_unit H hermitian time) denominatorComm
  have adjointComm : (denominator H time).conjTranspose * H = H * (denominator H time).conjTranspose := by
    simp only [denominator,Matrix.conjTranspose_add,Matrix.conjTranspose_one,generator_skew H hermitian time,
      Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,Matrix.neg_mul,Matrix.mul_neg,generatorComm]
  rw [step,Matrix.mul_assoc,adjointComm,← Matrix.mul_assoc,inverseComm,Matrix.mul_assoc]

theorem frozen_energy (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (density : Matrix n n ℂ) :
    Matrix.trace (H * densityUpdate H time density) = Matrix.trace (H * density) := by
  have unitary := (step_unitary H hermitian time).1
  change (step H time).conjTranspose * step H time = 1 at unitary
  have commutes := step_hamiltonian H hermitian time
  calc
    _ = Matrix.trace (step H time * (H * density) * (step H time).conjTranspose) := by
      congr 1
      simp only [densityUpdate,← Matrix.mul_assoc]
      rw [← commutes]
    _ = _ := by rw [Matrix.trace_mul_cycle,unitary,Matrix.one_mul]

end
end CPS1ElectronicEvolution
