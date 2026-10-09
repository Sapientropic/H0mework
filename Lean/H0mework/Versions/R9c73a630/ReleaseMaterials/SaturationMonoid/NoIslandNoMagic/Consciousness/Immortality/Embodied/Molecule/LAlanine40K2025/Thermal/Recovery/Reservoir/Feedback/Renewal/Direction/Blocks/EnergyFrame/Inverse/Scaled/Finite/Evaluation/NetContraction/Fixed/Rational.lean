import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Matrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators

abbrev MatrixQ (α β : Type*) := Matrix α β Scalar.QComplex

variable {α β γ δ : Type*}

def qvalue (A : MatrixQ α β) : Matrix α β ℂ := fun i j => Scalar.value (A i j)
def qmultiply [Fintype β] (A : MatrixQ α β) (B : MatrixQ β γ) : MatrixQ α γ :=
  fun i j => ∑ k, Scalar.multiply (A i k) (B k j)
def qadjoint (A : MatrixQ α β) : MatrixQ β α := fun i j => ((A j i).1,-(A j i).2)
def qkron (A : MatrixQ α β) (B : MatrixQ γ δ) : MatrixQ (α × γ) (β × δ) :=
  fun i j => Scalar.multiply (A i.1 j.1) (B i.2 j.2)

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → Scalar.QComplex) :
    Scalar.value (∑ i ∈ s, f i)=∑ i ∈ s, Scalar.value (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scalar.value]
  | @insert a s absent ih => simp only [Finset.sum_insert absent,Scalar.value_add,ih]

theorem qvalue_multiply [Fintype β] (A : MatrixQ α β) (B : MatrixQ β γ) :
    qvalue (qmultiply A B)=qvalue A*qvalue B := by
  ext i j
  simp only [qvalue,qmultiply,value_sum,Scalar.value_multiply,Matrix.mul_apply]

theorem qvalue_adjoint (A : MatrixQ α β) : qvalue (qadjoint A)=(qvalue A).conjTranspose := by
  ext i j
  simp [qvalue,qadjoint,Scalar.value]

theorem qvalue_kron (A : MatrixQ α β) (B : MatrixQ γ δ) : qvalue (qkron A B)=Matrix.kronecker (qvalue A) (qvalue B) := by
  ext i j
  exact Scalar.value_multiply _ _

def qreal (A : Matrix α β ℚ) : MatrixQ α β := fun i j => (A i j,0)

theorem qvalue_real (A : Matrix α β ℚ) : qvalue (qreal A)=(fun i j => (A i j : ℂ)) := by
  ext i j
  simp [qvalue,qreal,Scalar.value]

theorem qvalue_submatrix (A : MatrixQ α β) (f : γ → α) (g : δ → β) :
    qvalue (A.submatrix f g)=(qvalue A).submatrix f g := rfl


def roundRatio (n d : Int) : Int := (2*n+d)/(2*d)

theorem round_ratio_error (n d : Int) (positive : 0 < d) : 2*|n-d*roundRatio n d| ≤ d := by
  have denominator : 0 < 2*d := mul_pos (by norm_num) positive
  have lo := Int.ediv_mul_le (2*n+d) (ne_of_gt denominator)
  have hi := Int.lt_ediv_add_one_mul_self (2*n+d) denominator
  unfold roundRatio
  rcases le_total 0 (n-d*((2*n+d)/(2*d))) with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith

def quantizeScalar (z : ℚ) : Int := roundRatio (scale*z.num) z.den

def quantize (A : MatrixQ α β) : MatrixInt α β :=
  ⟨fun i j => quantizeScalar (A i j).1,fun i j => quantizeScalar (A i j).2⟩

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
