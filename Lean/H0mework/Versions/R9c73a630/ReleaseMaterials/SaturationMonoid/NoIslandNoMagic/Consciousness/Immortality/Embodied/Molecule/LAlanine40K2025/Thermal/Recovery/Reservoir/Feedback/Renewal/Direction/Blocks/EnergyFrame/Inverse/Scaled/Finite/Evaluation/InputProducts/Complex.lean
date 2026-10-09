import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.ResidualNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def complexMatrix {ι : Type*} (R I : Matrix ι ι Int) : Matrix ι ι ℂ :=
  fun i j => (R i j : ℂ)+Complex.I*(I i j : ℂ)

theorem complexMatrix_real {ι : Type*} (R : Matrix ι ι Int) : complexMatrix R 0=Cast.complexMatrix R := by
  ext i j
  simp [complexMatrix,Cast.complexMatrix]

theorem complexMatrix_add {ι : Type*} (R I A B : Matrix ι ι Int) :
    complexMatrix (R+A) (I+B)=complexMatrix R I+complexMatrix A B := by
  ext i j
  simp only [complexMatrix,Matrix.add_apply,Int.cast_add]
  ring

theorem complexMatrix_sub {ι : Type*} (R I A B : Matrix ι ι Int) :
    complexMatrix (R-A) (I-B)=complexMatrix R I-complexMatrix A B := by
  ext i j
  simp only [complexMatrix,Matrix.sub_apply,Int.cast_sub]
  ring

theorem complexMatrix_mul {ι : Type*} [Fintype ι] (R I A B : Matrix ι ι Int) :
    complexMatrix R I*complexMatrix A B=complexMatrix (R*A-I*B) (R*B+I*A) := by
  ext i j
  simp only [complexMatrix,Matrix.mul_apply,Matrix.sub_apply,Matrix.add_apply,Int.cast_sub,Int.cast_add,Int.cast_sum,Int.cast_mul]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  linear_combination ((I i k : ℂ)*(B k j : ℂ))*Complex.I_sq

theorem complexMatrix_star {ι : Type*} (R I : Matrix ι ι Int) :
    star (complexMatrix R I)=complexMatrix R.transpose (-I.transpose) := by
  ext i j
  simp [complexMatrix]

variable {ι : Type*}

def scaledMatrix (R I : Matrix ι ι Int) (d : Int) : Matrix ι ι ℂ := (d : ℂ)⁻¹ • complexMatrix R I

theorem scaledMatrix_entry (R I : Matrix ι ι Int) (d : Int) (i j : ι) :
    scaledMatrix R I d i j=((R i j : ℂ)+Complex.I*(I i j : ℂ))/(d : ℂ) := by
  simp only [scaledMatrix,Matrix.smul_apply,complexMatrix,smul_eq_mul,div_eq_mul_inv,mul_comm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
