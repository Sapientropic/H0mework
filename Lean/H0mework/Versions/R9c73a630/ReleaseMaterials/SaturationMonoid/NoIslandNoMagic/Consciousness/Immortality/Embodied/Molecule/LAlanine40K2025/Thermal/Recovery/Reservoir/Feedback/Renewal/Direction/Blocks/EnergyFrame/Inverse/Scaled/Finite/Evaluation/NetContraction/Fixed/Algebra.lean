import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Rational

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators
variable {α β γ : Type*}

def qscale (z : Scalar.QComplex) (A : MatrixQ α β) : MatrixQ α β := fun i j => Scalar.multiply z (A i j)
def qidentity (α : Type*) [Fintype α] [DecidableEq α] : MatrixQ α α := Matrix.scalar α (1,0)
def qscalar (α : Type*) [Fintype α] [DecidableEq α] (z : Scalar.QComplex) : MatrixQ α α := Matrix.scalar α z

theorem qvalue_scale (z : Scalar.QComplex) (A : MatrixQ α β) : qvalue (qscale z A)=Scalar.value z • qvalue A := by
  ext i j
  exact Scalar.value_multiply _ _

theorem qvalue_zero : qvalue (0 : MatrixQ α β)=0 := by
  ext i j
  simp [qvalue,Scalar.value]

theorem qvalue_add (A B : MatrixQ α β) : qvalue (A+B)=qvalue A+qvalue B := by
  ext i j
  exact Scalar.value_add _ _

theorem qvalue_sum {ι : Type*} (s : Finset ι) (A : ι → MatrixQ α β) :
    qvalue (∑ i ∈ s,A i)=∑ i ∈ s,qvalue (A i) := by
  ext i j
  simp only [qvalue,Matrix.sum_apply,value_sum]

theorem qvalue_scalar [Fintype α] [DecidableEq α] (z : Scalar.QComplex) : qvalue (qscalar α z)=Matrix.scalar α (Scalar.value z) := by
  ext i j
  by_cases same : i=j <;> simp [qvalue,qscalar,Matrix.scalar_apply,same,Scalar.value]

theorem qvalue_identity [Fintype α] [DecidableEq α] : qvalue (qidentity α)=1 := by
  change qvalue (qscalar α (1,0))=_
  rw [qvalue_scalar]
  simp [Scalar.value]

theorem qvalue_blocks (A : MatrixQ α α) (B : MatrixQ β β) :
    qvalue (Matrix.fromBlocks A 0 0 B)=Matrix.fromBlocks (qvalue A) 0 0 (qvalue B) := by
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j) <;> simp [qvalue,Matrix.fromBlocks,Scalar.value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
