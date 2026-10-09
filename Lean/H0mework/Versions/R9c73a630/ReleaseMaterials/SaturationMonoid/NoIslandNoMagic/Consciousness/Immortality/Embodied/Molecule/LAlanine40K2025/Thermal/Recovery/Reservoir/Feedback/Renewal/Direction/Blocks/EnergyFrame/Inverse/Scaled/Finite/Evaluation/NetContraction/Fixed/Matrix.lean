import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Compact

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators Matrix.Norms.L2Operator

def scale : Int := 10^30

def round (x : Int) : Int := (2*x+scale)/(2*scale)

theorem scale_positive : 0 < scale := by decide

theorem round_residual (x : Int) : 2*|x-scale*round x| ≤ scale := by
  have positive : (0 : Int) < 2*scale := mul_pos (by norm_num) scale_positive
  have lo := Int.ediv_mul_le (2*x+scale) (ne_of_gt positive)
  have hi := Int.lt_ediv_add_one_mul_self (2*x+scale) positive
  change 2*|x-scale*((2*x+scale)/(2*scale))| ≤ scale
  rcases le_total 0 (x-scale*((2*x+scale)/(2*scale))) with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith

structure MatrixInt (α β : Type*) where
  re : Matrix α β Int
  im : Matrix α β Int

variable {α β γ : Type*}

def raw (A : MatrixInt α β) : Matrix α β ℂ := fun i j => (A.re i j : ℂ)+Complex.I*(A.im i j : ℂ)
noncomputable def value (A : MatrixInt α β) : Matrix α β ℂ := (scale : ℂ)⁻¹ • raw A

def add (A B : MatrixInt α β) : MatrixInt α β := ⟨A.re+B.re,A.im+B.im⟩
def sub (A B : MatrixInt α β) : MatrixInt α β := ⟨A.re-B.re,A.im-B.im⟩
def adjoint (A : MatrixInt α β) : MatrixInt β α := ⟨A.re.transpose,-A.im.transpose⟩
def submatrix (A : MatrixInt α β) (f : γ → α) {δ : Type*} (g : δ → β) : MatrixInt γ δ :=
  ⟨A.re.submatrix f g,A.im.submatrix f g⟩

def multiply [Fintype β] (A : MatrixInt α β) (B : MatrixInt β γ) : MatrixInt α γ :=
  ⟨fun i j => round ((A.re*B.re-A.im*B.im) i j),fun i j => round ((A.re*B.im+A.im*B.re) i j)⟩

theorem raw_mul [Fintype β] (A : MatrixInt α β) (B : MatrixInt β γ) :
    raw A*raw B=raw ⟨A.re*B.re-A.im*B.im,A.re*B.im+A.im*B.re⟩ := by
  ext i j
  simp only [raw,Matrix.mul_apply,Matrix.sub_apply,Matrix.add_apply,Int.cast_sub,Int.cast_add,Int.cast_sum,Int.cast_mul]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  linear_combination ((A.im i k : ℂ)*(B.im k j : ℂ))*Complex.I_sq

theorem value_add (A B : MatrixInt α β) : value (add A B)=value A+value B := by
  ext i j
  simp only [value,raw,add,Matrix.smul_apply,Matrix.add_apply,Int.cast_add,smul_eq_mul]
  ring

theorem value_sub (A B : MatrixInt α β) : value (sub A B)=value A-value B := by
  ext i j
  simp only [value,raw,sub,Matrix.smul_apply,Matrix.sub_apply,Int.cast_sub,smul_eq_mul]
  ring

theorem value_adjoint (A : MatrixInt α β) : value (adjoint A)=(value A).conjTranspose := by
  ext i j
  simp [value,raw,adjoint]

theorem value_submatrix (A : MatrixInt α β) (f : γ → α) {δ : Type*} (g : δ → β) :
    value (submatrix A f g)=(value A).submatrix f g := rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
